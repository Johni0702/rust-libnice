/// See [test::connects_and_transmits_data] for a usage example.
use crate::ffi;
use futures::sync::mpsc;
use futures::Async;
use futures::AsyncSink;
use futures::Future;
use futures::Poll;
use futures::Sink;
use futures::Stream as FuturesStream;
use libnice_sys as sys;
use std::collections::HashMap;
use std::ffi::CString;
use std::io;
use std::sync::Arc;
use std::sync::Mutex;

pub use crate::ffi::BoolResult;
pub use crate::ffi::NiceCompatibility;
pub use crate::ffi::NiceComponentState as ComponentState;
pub use webrtc_sdp::attribute_type::SdpAttributeCandidate as Candidate;

type ComponentId = (sys::guint, sys::guint);

/// A single, high-level ICE agent.
///
/// **Note**: The agent implements [Stream] and needs to be [`poll()`ed] for any of its [Stream]s
///           to make progress.
///
/// [`poll()`ed]: Future::poll
pub struct Agent {
    ctx: ffi::GMainContext,
    agent: ffi::NiceAgent,
    main_loop: ffi::GMainLoop,
    msgs_sender: mpsc::UnboundedSender<ControlMsg>,
    msgs: mpsc::UnboundedReceiver<ControlMsg>,
    candidate_sinks: Arc<Mutex<HashMap<sys::guint, mpsc::UnboundedSender<Candidate>>>>,
    state_sinks: Arc<Mutex<HashMap<ComponentId, mpsc::Sender<ComponentState>>>>,
}

impl Agent {
    /// Creates a new ICE agent in RFC5245 (ICE) compatibility mode.
    pub fn new_rfc5245() -> Self {
        Self::new(NiceCompatibility::RFC5245)
    }

    /// Creates a new ICE agent with the specified compatibility mode.
    pub fn new(compat: NiceCompatibility) -> Self {
        // Initialize FFI structs
        let ctx = ffi::GMainContext::new();
        let main_loop = ffi::GMainLoop::new(&ctx);
        let mut agent = ffi::NiceAgent::new(&ctx, compat);

        // Start main loop on new thread
        let main_loop_clone = main_loop.clone();
        std::thread::spawn(move || {
            main_loop_clone.run();
        });

        // Channel for sending messages from streams to the agent
        let (msgs_sender, msgs) = mpsc::unbounded();

        // Channel for sending candidates to streams
        let candidate_sinks: Arc<Mutex<HashMap<sys::guint, mpsc::UnboundedSender<Candidate>>>> =
            Default::default();
        let candidate_sinks_clone = Arc::clone(&candidate_sinks);
        agent
            .on_new_candidate(move |candidate| {
                let mut candidate_sinks = candidate_sinks_clone.lock().unwrap();
                let stream_id = &candidate.stream_id();
                if let Some(sink) = candidate_sinks.get_mut(stream_id) {
                    if sink.unbounded_send(candidate.to_sdp()).is_err() {
                        candidate_sinks.remove(stream_id);
                    }
                }
            })
            .unwrap();
        let candidate_sinks_clone = Arc::clone(&candidate_sinks);
        agent
            .on_candidate_gathering_done(move |stream_id| {
                let mut candidate_sinks = candidate_sinks_clone.lock().unwrap();
                candidate_sinks.remove(&stream_id);
            })
            .unwrap();

        // Channel for sending state updates to components
        let state_sinks: Arc<Mutex<HashMap<ComponentId, mpsc::Sender<ComponentState>>>> =
            Default::default();
        let state_sinks_clone = Arc::clone(&state_sinks);
        agent
            .on_component_state_changed(move |stream_id, component_id, new_state| {
                let mut state_sinks = state_sinks_clone.lock().unwrap();
                let key = (stream_id, component_id);
                if let Some(sink) = state_sinks.get_mut(&key) {
                    if sink.send(new_state).wait().is_err() {
                        state_sinks.remove(&key);
                    }
                }
            })
            .unwrap();

        Agent {
            ctx,
            agent,
            main_loop,
            msgs_sender,
            msgs,
            candidate_sinks,
            state_sinks,
        }
    }

    /// Returns the low-level context this agent is running on.
    pub fn get_ffi_ctx(&self) -> &ffi::GMainContext {
        &self.ctx
    }

    /// Returns the low-level agent backing this Agent.
    pub fn get_ffi_agent(&mut self) -> &mut ffi::NiceAgent {
        &mut self.agent
    }

    /// See the [libnice] documentation for more info.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-software
    pub fn set_software(&mut self, name: impl Into<String>) {
        let name = CString::new(name.into()).expect("name must not have have null bytes");
        self.agent.set_software(name);
    }

    /// Changes whether this agent is in controlling mode (by default it is not).
    pub fn set_controlling_mode(&mut self, controlling: bool) {
        self.agent.set_controlling_mode(controlling);
    }

    /// Add a new [Stream] with the specified amount of components to the agent.
    pub fn stream_builder(&mut self, components: usize) -> StreamBuilder {
        StreamBuilder::new(self, components)
    }

    fn handle_msg(&mut self, msg: ControlMsg) {
        match msg {
            ControlMsg::SetRemoteCredentials(stream_id, ufrag, pwd) => {
                let _ = self.agent.set_remote_credentials(stream_id, &ufrag, &pwd);
            }
            ControlMsg::AddRemoteCandidate((stream_id, component_id), candidate) => {
                let candidate = ffi::NiceCandidate::from_sdp(&candidate);
                let candidate = candidate.as_ref();
                let candidates = std::slice::from_ref(&candidate);
                let _ = self
                    .agent
                    .add_remote_candidates(stream_id, component_id, candidates);
            }
            ControlMsg::Send((stream_id, component_id), buf) => {
                // The libnice docs are very unclear on when this can fail with unreliable
                // transports, so we'll just assume it only fails for WOULD_BLOCK.
                let _ = self.agent.send(stream_id, component_id, &buf);
            }
        }
    }
}

impl Drop for Agent {
    fn drop(&mut self) {
        self.main_loop.quit();
    }
}

impl Future for Agent {
    type Item = (); // never
    type Error = (); // never
    fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
        loop {
            match self.msgs.poll() {
                Ok(Async::NotReady) => break,
                Ok(Async::Ready(Some(msg))) => {
                    self.handle_msg(msg);
                }
                Ok(Async::Ready(None)) => unreachable!(),
                Err(()) => unreachable!(),
            }
        }
        Ok(Async::NotReady)
    }
}

/// Builder for ICE [Stream]s.
pub struct StreamBuilder<'a> {
    agent: &'a mut Agent,
    components: sys::guint,
    inbound_buf_size: usize,
    port_ranges: HashMap<usize, (u16, u16)>,
}

impl<'a> StreamBuilder<'a> {
    /// See [Agent::stream_builder].
    pub fn new(agent: &'a mut Agent, components: usize) -> Self {
        Self {
            agent,
            components: components as sys::guint,
            inbound_buf_size: 10,
            port_ranges: HashMap::new(),
        }
    }

    /// Sets the size of the buffer used to store inbound packets.
    pub fn set_inbound_buffer_size(&mut self, size: usize) -> &mut Self {
        self.inbound_buf_size = size;
        self
    }

    /// Limits the range of ports used for host candidates.
    ///
    /// If the range is exhausted, [build] will fail.
    /// To set the range per component, use [set_component_port_range].
    pub fn set_port_range(
        &mut self,
        min_port: u16,
        max_port: u16,
    ) -> &mut Self {
        for i in 0..self.components as usize {
            self.port_ranges.insert(i, (min_port, max_port));
        }
        self
    }

    /// Limits the range of ports used for host candidates for the component at the specified index.
    /// Note that the first component (with id `1`) is at index `0`.
    ///
    /// If the range is exhausted, [build] will fail.
    /// To set the range for all components, use [set_port_range].
    ///
    /// # Panics
    ///
    /// Panics if `component_index >= components`.
    pub fn set_component_port_range(
        &mut self,
        component_index: usize,
        min_port: u16,
        max_port: u16,
    ) -> &mut Self {
        if component_index >= self.components as usize {
            panic!(
                "index {} of of range (size: {})",
                component_index, self.components
            );
        }
        self.port_ranges.insert(component_index, (min_port, max_port));
        self
    }

    /// Build the [Stream].
    pub fn build(&mut self) -> BoolResult<Stream> {
        let agent = &mut self.agent;
        let state_sinks = &mut agent.state_sinks;
        let ffi = &mut agent.agent;

        let id = ffi.add_stream(self.components)?;
        let (local_ufrag, local_pwd) = ffi.get_local_credentials(id).expect("local credentials");
        let local_ufrag = local_ufrag
            .into_string()
            .expect("generated ufrag is valid utf8");
        let local_pwd = local_pwd
            .into_string()
            .expect("generated pwd is valid utf8");

        let mut components = Vec::new();
        for i in 0..self.components {
            let component_id = i + 1;
            let (mut source_sender, source) = mpsc::channel(self.inbound_buf_size);
            ffi.attach_recv(id, component_id, &agent.ctx, move |buf| {
                let _ = source_sender.try_send(buf.to_vec());
            })?;

            let (state_sender, state_stream) = mpsc::channel(8);
            state_sinks
                .lock()
                .unwrap()
                .insert((id, component_id), state_sender);

            components.push(StreamComponent {
                stream_id: id,
                component_id,
                state: ComponentState::Disconnected,
                state_stream,
                source,
                sink: agent.msgs_sender.clone(),
            });
        }

        let (candidate_sink, candidates) = mpsc::unbounded();
        agent
            .candidate_sinks
            .lock()
            .unwrap()
            .insert(id, candidate_sink);

        for (index, (min_port, max_port)) in &self.port_ranges {
            ffi.set_port_range(id, *index as sys::guint + 1, *min_port, *max_port);
        }

        ffi.gather_candidates(id)?;

        Ok(Stream {
            id,
            local_ufrag,
            local_pwd,
            msg_sink: agent.msgs_sender.clone(),
            candidates,
            components,
        })
    }
}

enum ControlMsg {
    SetRemoteCredentials(sys::guint, CString, CString),
    AddRemoteCandidate(ComponentId, Candidate),
    Send(ComponentId, Vec<u8>),
}

/// An ICE stream consisting of multiple components.
///
/// Implements [futures::Stream] which emits the local ICE candidates for this stream as they are
/// being discovered.
pub struct Stream {
    id: sys::guint,
    local_ufrag: String,
    local_pwd: String,
    msg_sink: mpsc::UnboundedSender<ControlMsg>,
    candidates: mpsc::UnboundedReceiver<Candidate>,
    components: Vec<StreamComponent>,
}

impl Stream {
    /// See [Agent::stream_builder].
    pub fn builder(agent: &mut Agent, components: usize) -> StreamBuilder {
        StreamBuilder::new(agent, components)
    }

    /// Returns the local STUN ufrag for this stream.
    pub fn get_local_ufrag(&self) -> &str {
        &self.local_ufrag
    }

    /// Returns the local STUN pwd for this stream.
    pub fn get_local_pwd(&self) -> &str {
        &self.local_pwd
    }

    /// Set the remote STUN credentials for this stream.
    pub fn set_remote_credentials(&mut self, ufrag: CString, pwd: CString) {
        let msg = ControlMsg::SetRemoteCredentials(self.id, ufrag, pwd);
        let _ = self.msg_sink.unbounded_send(msg);
    }

    /// Adds a new remote ICE candidate for this stream.
    pub fn add_remote_candidate(&mut self, candidate: Candidate) {
        let msg = ControlMsg::AddRemoteCandidate((self.id, candidate.component), candidate);
        let _ = self.msg_sink.unbounded_send(msg);
    }

    /// Returns a references to the components of this stream.
    pub fn components(&self) -> &[StreamComponent] {
        &self.components
    }

    /// Returns a mutable references to the components of this stream.
    pub fn mut_components(&mut self) -> &mut [StreamComponent] {
        &mut self.components
    }

    /// Returns the components of this stream, returning an empty Vec on subsequent calls.
    pub fn take_components(&mut self) -> Vec<StreamComponent> {
        std::mem::replace(&mut self.components, Vec::new())
    }

    /// Returns the components of this stream, consuming the stream.
    ///
    /// Note that this should probably only be called after all ICE candidates have been exchanged.
    /// Until then, use [Stream::mut_components] or [Stream::take_components] instead.
    pub fn into_components(self) -> Vec<StreamComponent> {
        self.components
    }
}

impl FuturesStream for Stream {
    type Item = Candidate;
    type Error = (); // never
    fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
        self.candidates.poll()
    }
}

/// A single ICE stream component.
/// It implements [Stream]+[Sink] as well as [AsyncRead]+[AsyncWrite].
///
/// [AsyncRead]: tokio_io::AsyncRead
/// [AsyncWrite]: tokio_io::AsyncWrite
pub struct StreamComponent {
    stream_id: sys::guint,
    component_id: sys::guint,
    state: ComponentState,
    state_stream: mpsc::Receiver<ComponentState>,
    source: mpsc::Receiver<Vec<u8>>,
    sink: mpsc::UnboundedSender<ControlMsg>,
}

impl StreamComponent {
    /// Adds a remote ICE candidate to this stream component.
    pub fn add_remote_candidate(&mut self, candidate: Candidate) {
        let msg = ControlMsg::AddRemoteCandidate((self.stream_id, self.component_id), candidate);
        let _ = self.sink.unbounded_send(msg);
    }

    /// Sends a packet of data via this component.
    ///
    /// Note that the [Agent] needs to be `poll()`ed for sending to make progress.
    pub fn unbounded_send(&mut self, item: Vec<u8>) {
        let msg = ControlMsg::Send((self.stream_id, self.component_id), item);
        let _ = self.sink.unbounded_send(msg);
    }

    /// Returns the current state of this component.
    ///
    /// Note that the returned state only reflects the state of this stream at the last time it
    /// was `poll()`ed by reading or [StreamComponent::wait_for_state].
    pub fn get_state(&self) -> ComponentState {
        self.state
    }

    /// Returns a future which waits until the component is in the target state or has surpassed
    /// the target state (e.g. waiting for Connected will also be done when the state is Ready).
    ///
    /// The returned future will fail if the agent or the stream is closed or the component
    /// switches to Failed state.
    pub fn wait_for_state(self, target: ComponentState) -> ComponentStateFuture {
        ComponentStateFuture {
            component: Some(self),
            target,
        }
    }

    /// Updates the current state by polling [state_stream].
    /// Returns `Err(())` if [state_stream] has been closed.
    fn poll_state(&mut self) -> Result<(), ()> {
        loop {
            match self.state_stream.poll()? {
                Async::NotReady => return Ok(()),
                Async::Ready(Some(new_state)) => {
                    self.state = new_state;
                }
                Async::Ready(None) => return Err(()),
            }
        }
    }
}

/// Future returned by [StreamComponent::wait_for_state]
pub struct ComponentStateFuture {
    component: Option<StreamComponent>,
    target: ComponentState,
}

impl Future for ComponentStateFuture {
    type Item = StreamComponent;
    type Error = (); // stream (or agent) has been closed
    fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
        fn rate(state: ComponentState) -> u8 {
            match state {
                ComponentState::Disconnected => 0,
                ComponentState::Gathering => 1,
                ComponentState::Connecting => 2,
                ComponentState::Connected => 3,
                ComponentState::Ready => 4,
                ComponentState::Failed => 5,
            }
        }
        let component = self.component.as_mut().expect("poll called after Ready");
        component.poll_state()?;
        if rate(component.state) >= rate(self.target) {
            if component.state == ComponentState::Failed {
                Err(())
            } else {
                Ok(Async::Ready(self.component.take().unwrap()))
            }
        } else {
            Ok(Async::NotReady)
        }
    }
}

impl FuturesStream for StreamComponent {
    type Item = Vec<u8>;
    type Error = (); // never
    fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
        if self.poll_state().is_err() {
            return Ok(Async::Ready(None));
        }
        self.source.poll().map_err(|()| unreachable!())
    }
}

impl Sink for StreamComponent {
    type SinkItem = Vec<u8>;
    type SinkError = (); // never
    fn start_send(
        &mut self,
        item: Self::SinkItem,
    ) -> Result<AsyncSink<Self::SinkItem>, Self::SinkError> {
        let msg = ControlMsg::Send((self.stream_id, self.component_id), item);
        let _ = self.sink.unbounded_send(msg);
        Ok(AsyncSink::Ready)
    }

    fn poll_complete(&mut self) -> Poll<(), Self::SinkError> {
        Ok(Async::Ready(()))
    }
}

impl io::Read for StreamComponent {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.poll() {
            Ok(Async::Ready(Some(vec))) => vec.as_slice().read(buf),
            Ok(Async::Ready(None)) => Ok(0),
            Ok(Async::NotReady) => Err(io::ErrorKind::WouldBlock.into()),
            Err(()) => unreachable!(),
        }
    }
}
impl tokio_io::AsyncRead for StreamComponent {}

impl io::Write for StreamComponent {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let _ = self.start_send(buf.to_vec());
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
impl tokio_io::AsyncWrite for StreamComponent {
    fn shutdown(&mut self) -> Poll<(), io::Error> {
        Ok(Async::Ready(()))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use tokio::runtime::current_thread::Runtime;

    #[test]
    fn connects_and_transmits_data() {
        let mut executor = Runtime::new().unwrap();

        // Create ICE agents
        let mut server = Agent::new_rfc5245();
        let mut client = Agent::new_rfc5245();
        client.set_controlling_mode(true);

        // Create one ICE stream per agent, each with one component
        let mut server_stream = server.stream_builder(1).build().unwrap();
        let mut client_stream = client.stream_builder(1).build().unwrap();

        // Grab components for later use (you could also ship them off to different tasks here)
        let mut server_component = server_stream.take_components().pop().unwrap();
        let mut client_component = client_stream.take_components().pop().unwrap();

        // Exchange ICE credentials
        server_stream.set_remote_credentials(
            CString::new(client_stream.get_local_ufrag()).unwrap(),
            CString::new(client_stream.get_local_pwd()).unwrap(),
        );
        client_stream.set_remote_credentials(
            CString::new(server_stream.get_local_ufrag()).unwrap(),
            CString::new(server_stream.get_local_pwd()).unwrap(),
        );

        // Poll agents to make connection (and candidate-gathering) progress
        // Note: Normally you'd want some way to drop the agent once you no longer need it,
        //       here we just drop the executor once we're done.
        executor.spawn(server);
        executor.spawn(client);

        // Exchange ICE candidates
        // Note that the connection might already start working before all have been exchanged
        // but continuing might improve the network path taken and provide fallback options.
        for candidate in executor.block_on(server_stream.by_ref().collect()).unwrap() {
            println!("Server candidate: {}", candidate.to_string());
            client_stream.add_remote_candidate(candidate);
        }
        for candidate in executor.block_on(client_stream.by_ref().collect()).unwrap() {
            println!("Client candidate: {}", candidate.to_string());
            server_stream.add_remote_candidate(candidate);
        }

        // Wait until the component state reaches Connected, otherwise data will just be dropped
        server_component = executor
            .block_on(server_component.wait_for_state(ComponentState::Connected))
            .unwrap();
        client_component = executor
            .block_on(client_component.wait_for_state(ComponentState::Connected))
            .unwrap();

        // Send some data (potentially unreliable, hence unbounded)
        server_component.unbounded_send(vec![1, 2, 3, 4]);
        client_component.unbounded_send(vec![42]);

        // Check that we received it
        // Note that we can be fairly sure here (local-to-local) but under normal circumstances
        // the transport must be assumed to be unreliable!
        assert_eq!(
            Some(vec![42]),
            executor
                .block_on(server_component.by_ref().into_future())
                .map_err(|_| unreachable!())
                .unwrap()
                .0
        );
        assert_eq!(
            Some(vec![1, 2, 3, 4]),
            executor
                .block_on(client_component.by_ref().into_future())
                .map_err(|_| unreachable!())
                .unwrap()
                .0
        );
    }
}
