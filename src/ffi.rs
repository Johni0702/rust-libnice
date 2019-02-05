use foreign_types::foreign_type;
use foreign_types::ForeignTypeRef;
use std::any::Any;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::ffi::CStr;
use std::ffi::CString;
use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::SocketAddr;
use std::ops::DerefMut;
use std::os::raw::c_char;
use std::ptr;
use webrtc_sdp::attribute_type::SdpAttributeCandidate;
use webrtc_sdp::attribute_type::SdpAttributeCandidateTcpType;
use webrtc_sdp::attribute_type::SdpAttributeCandidateTransport;
use webrtc_sdp::attribute_type::SdpAttributeCandidateType;

use libnice_sys as sys;

foreign_type! {
    type CType = sys::GMainContext;
    fn drop = sys::g_main_context_unref;
    fn clone = sys::g_main_context_ref;
    /// See the [glib] documentation.
    ///
    /// [glib]: https://developer.gnome.org/glib/stable/glib-The-Main-Event-Loop.html#GMainContext
    pub struct GMainContext;
    /// Reference to [GMainContext].
    pub struct GMainContextRef;
}
unsafe impl Send for GMainContext {}

impl GMainContext {
    /// Creates a new GMainContext
    pub fn new() -> Self {
        Self(unsafe { sys::g_main_context_new() })
    }
}

impl Default for GMainContext {
    fn default() -> Self {
        Self::new()
    }
}

impl GMainContextRef {
    /// See the [glib] documentation.
    ///
    /// [glib]: https://developer.gnome.org/glib/stable/glib-The-Main-Event-Loop.html#g-main-context-acquire
    pub fn acquire(&self) -> Option<AcquiredGMainContext> {
        if unsafe { sys::g_main_context_acquire(self.as_ptr()) != 0 } {
            Some(AcquiredGMainContext(&self))
        } else {
            None
        }
    }
}

/// A [GMainContextRef] which has been acquired by a call to [GMainContextRef::acquire] and will be
/// released once dropped.
pub struct AcquiredGMainContext<'a>(&'a GMainContextRef);
impl<'a> Drop for AcquiredGMainContext<'a> {
    fn drop(&mut self) {
        unsafe { sys::g_main_context_release(self.0.as_ptr()) }
    }
}

foreign_type! {
    type CType = sys::GMainLoop;
    fn drop = sys::g_main_loop_unref;
    fn clone = sys::g_main_loop_ref;
    /// See the [glib] documentation.
    ///
    /// [glib]: https://developer.gnome.org/glib/stable/glib-The-Main-Event-Loop.html
    pub struct GMainLoop;
    /// Reference to [GMainLoop].
    pub struct GMainLoopRef;
}
unsafe impl Send for GMainLoop {}

impl GMainLoop {
    /// Creates a new GMainLoop.
    pub fn new(ctx: &GMainContextRef) -> Self {
        Self(unsafe { sys::g_main_loop_new(ctx.as_ptr(), 0) })
    }
}

impl GMainLoopRef {
    /// Returns the context of this loop.
    pub fn get_context(&self) -> &GMainContextRef {
        unsafe { GMainContextRef::from_ptr(sys::g_main_loop_get_context(self.as_ptr())) }
    }

    /// Runs the loop, blocking this thread until [GMainLoopRef::quit] is called.
    pub fn run(&self) {
        let acquired_ctx = self
            .get_context()
            .acquire()
            .expect("failed to acquire context");
        unsafe { sys::g_main_loop_run(self.as_ptr()) }
        std::mem::drop(acquired_ctx);
    }

    /// Stops the loop.
    ///
    /// See [GMainLoopRef::run]
    pub fn quit(&self) {
        unsafe { sys::g_main_loop_quit(self.as_ptr()) }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html
pub struct NiceAgent {
    ptr: *mut sys::NiceAgent,
    recv_callbacks: HashMap<(sys::guint, sys::guint), Box<Any>>,
}

/// Either `Ok(T)` or `Err` with a string description of the function that failed.
///
/// Many libnice functions only return a single boolean to indicate failure. This Result type
/// is used for such functions where no better alternative exists.
pub type BoolResult<T> = Result<T, &'static str>;

impl NiceAgent {
    /// Creates a new NiceAgent in RFC5245 compatibility mode.
    pub fn new_rfc5245(ctx: &GMainContextRef) -> NiceAgent {
        Self::new(ctx, NiceCompatibility::RFC5245)
    }

    /// Creates a new NiceAgent with the specified compatibility mode.
    pub fn new(ctx: &GMainContextRef, compat: NiceCompatibility) -> NiceAgent {
        let ptr = unsafe { sys::nice_agent_new(ctx.as_ptr(), compat as u32) };
        if ptr.is_null() {
            panic!("nice_agent_new failed");
        }
        NiceAgent {
            ptr,
            recv_callbacks: HashMap::new(),
        }
    }

    /// Returns a pointer to the raw nice agent.
    ///
    /// # Safety
    /// All FFI caveats apply. Additionally, the raw NiceAgent must not outlive `self`
    /// (i.e. no calling of g_object_ref) because `self` keeps references to callback functions
    /// which would then be dangling after it has been dropped.
    pub fn as_ptr(&self) -> *mut sys::NiceAgent {
        self.ptr
    }

    /// Returns a pointer to the raw nice agent as a [sys::GObject].
    ///
    /// # Safety
    /// See [NiceAgent::as_ptr].
    #[allow(clippy::cast_ptr_alignment)] // libnice should always return properly aligned pointers
    pub fn as_gobject_ptr(&self) -> *mut sys::GObject {
        self.ptr as *mut sys::GObject
    }

    /// Attaches a callback function to the specified signal.
    pub fn on_signal<UserData: Send + 'static>(
        &mut self,
        signal: &str,
        wrapper: extern "C" fn(),
        user_data: UserData,
    ) -> BoolResult<()> {
        extern "C" fn drop<UserData>(user_data: sys::gpointer, _closure: *mut sys::GClosure) {
            let user_data = user_data as *mut UserData;
            let boxed_user_data = unsafe { Box::from_raw(user_data) };
            std::mem::drop(boxed_user_data);
        }
        let signal = CString::new(signal).expect("valid signal name");
        let res = unsafe {
            sys::g_signal_connect_data(
                self.ptr as sys::gpointer,
                signal.as_ptr(),
                Some(wrapper),
                Box::into_raw(Box::new(user_data)) as sys::gpointer,
                Some(drop::<UserData>),
                0,
            )
        };
        if res == 0 {
            return Err("g_signal_connect_data failed");
        }
        Ok(())
    }

    /// Attaches a callback function to the `new-candidate-full` signal.
    pub fn on_new_candidate<F: FnMut(&NiceCandidateRef) + Send + 'static>(
        &mut self,
        f: F,
    ) -> BoolResult<()> {
        extern "C" fn wrapper<F: FnMut(&NiceCandidateRef) + Send + 'static>(
            _agent: *mut sys::NiceAgent,
            candidate: *mut sys::NiceCandidate,
            user_data: sys::gpointer,
        ) {
            let f_ptr = user_data as *mut F;
            let f = unsafe { &mut *f_ptr };
            let candidate = unsafe { NiceCandidateRef::from_ptr(candidate) };
            f(candidate)
        }
        self.on_signal(
            "new-candidate-full",
            unsafe { std::mem::transmute::<extern "C" fn(_, _, _), extern "C" fn()>(wrapper::<F>) },
            f,
        )
    }

    /// Attaches a callback function to the `candidate-gathering-done` signal.
    pub fn on_candidate_gathering_done<F: FnMut(sys::guint) + Send + 'static>(
        &mut self,
        f: F,
    ) -> BoolResult<()> {
        extern "C" fn wrapper<F: FnMut(sys::guint) + Send + 'static>(
            _agent: *mut sys::NiceAgent,
            stream_id: sys::guint,
            user_data: sys::gpointer,
        ) {
            let f_ptr = user_data as *mut F;
            let f = unsafe { &mut *f_ptr };
            f(stream_id)
        }
        self.on_signal(
            "candidate-gathering-done",
            unsafe { std::mem::transmute::<extern "C" fn(_, _, _), extern "C" fn()>(wrapper::<F>) },
            f,
        )
    }

    /// Attaches a callback function to the `component-state-changed` signal.
    pub fn on_component_state_changed<
        F: FnMut(sys::guint, sys::guint, NiceComponentState) + Send + 'static,
    >(
        &mut self,
        f: F,
    ) -> BoolResult<()> {
        extern "C" fn wrapper<
            F: FnMut(sys::guint, sys::guint, NiceComponentState) + Send + 'static,
        >(
            _agent: *mut sys::NiceAgent,
            stream_id: sys::guint,
            component_id: sys::guint,
            state: sys::guint,
            user_data: sys::gpointer,
        ) {
            let f_ptr = user_data as *mut F;
            let f = unsafe { &mut *f_ptr };
            f(stream_id, component_id, state.into())
        }
        self.on_signal(
            "component-state-changed",
            unsafe {
                std::mem::transmute::<extern "C" fn(_, _, _, _, _), extern "C" fn()>(wrapper::<F>)
            },
            f,
        )
    }

    /// Sets the specified property.
    /// # Safety
    /// The property name and value pointers must be valid, the property must exist and the value
    /// must be of the correct type.
    pub unsafe fn set_property(&mut self, name: *const sys::gchar, value: *const sys::GValue) {
        sys::g_object_set_property(self.as_gobject_ptr(), name, value);
    }

    /// See the [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-software
    pub fn set_software(&self, name: impl Borrow<CStr>) {
        unsafe { sys::nice_agent_set_software(self.ptr, name.borrow().as_ptr()) }
    }

    /// Changes whether this agent is in controlling mode (by default it is not).
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#NiceAgent--controlling-mode
    pub fn set_controlling_mode(&mut self, controlling: bool) {
        unsafe {
            let mut value = new_g_value(G_TYPE_BOOLEAN);
            sys::g_value_set_boolean(&mut value, controlling as i32);
            self.set_property(
                "controlling-mode\0" as *const str as *const sys::gchar,
                &value,
            );
        }
    }

    /// Adds a new stream to this agent and returns its id.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-add-stream
    pub fn add_stream(&self, components: sys::guint) -> BoolResult<sys::guint> {
        let id = unsafe { sys::nice_agent_add_stream(self.ptr, components) };
        if id == 0 {
            return Err("add_stream failed");
        }
        Ok(id)
    }

    /// Starts candidate gathering for a stream.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-gather-candidates
    pub fn gather_candidates(&self, stream_id: sys::guint) -> BoolResult<()> {
        if unsafe { sys::nice_agent_gather_candidates(self.ptr, stream_id) } == 0 {
            return Err("gather_candidates failed");
        }
        Ok(())
    }

    /// Sets the remote ICE credentials for a stream.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-remote-credentials
    pub fn set_remote_credentials(
        &self,
        stream_id: sys::guint,
        ufrag: &CStr,
        pwd: &CStr,
    ) -> BoolResult<()> {
        if unsafe {
            sys::nice_agent_set_remote_credentials(
                self.ptr,
                stream_id,
                ufrag.as_ptr(),
                pwd.as_ptr(),
            )
        } == 0
        {
            return Err("set_remote_credentials failed");
        }
        Ok(())
    }

    /// Returns the local ICE credentials as `(ufrag, pwd)`.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-get-local-credentials
    pub fn get_local_credentials(&self, stream_id: sys::guint) -> BoolResult<(CString, CString)> {
        let mut ufrag_ptr: *mut c_char = ptr::null_mut();
        let mut pwd_ptr: *mut c_char = ptr::null_mut();
        if unsafe {
            sys::nice_agent_get_local_credentials(self.ptr, stream_id, &mut ufrag_ptr, &mut pwd_ptr)
        } == 0
        {
            return Err("set_remote_credentials failed");
        }
        let ufrag = unsafe { CStr::from_ptr(ufrag_ptr) }.to_owned();
        let pwd = unsafe { CStr::from_ptr(pwd_ptr) }.to_owned();
        unsafe {
            sys::g_free(ufrag_ptr as sys::gpointer);
            sys::g_free(pwd_ptr as sys::gpointer);
        }
        Ok((ufrag, pwd))
    }

    /// Adds a remote ICE candidate for a particular stream component.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-remote-candidates
    pub fn add_remote_candidates(
        &self,
        stream_id: sys::guint,
        component_id: sys::guint,
        candidates: &[&NiceCandidateRef],
    ) -> BoolResult<usize> {
        let mut list_entries = candidates
            .iter()
            .map(|item| sys::GSList {
                data: item.as_ptr() as sys::gpointer,
                next: ptr::null_mut(),
            })
            .collect::<Vec<_>>();
        list_entries
            .iter_mut()
            .fold(ptr::null_mut(), |next, entry| {
                (*entry).next = next;
                entry as *mut sys::GSList
            });
        // FIXME what does this function actually do? the docs talk about add but its name says set
        let res = unsafe {
            sys::nice_agent_set_remote_candidates(
                self.ptr,
                stream_id,
                component_id,
                list_entries
                    .last()
                    .map_or_else(ptr::null, |head| head as *const sys::GSList),
            )
        };
        if res < 0 {
            return Err("set_remote_candidates failed");
        }
        Ok(res as usize)
    }

    /// Sends data via the specified stream component.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-send
    pub fn send(
        &self,
        stream_id: sys::guint,
        component_id: sys::guint,
        buf: &[u8],
    ) -> Option<usize> {
        let res = unsafe {
            sys::nice_agent_send(
                self.ptr,
                stream_id,
                component_id,
                buf.len() as sys::guint,
                buf.as_ptr() as *const i8,
            )
        };
        if res < 0 {
            return None;
        }
        Some(res as usize)
    }

    /// Attaches a callback which gets passed any incoming packets for the specified stream
    /// component.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-attach-recv
    pub fn attach_recv<F: FnMut(&[u8]) + Send + 'static>(
        &mut self,
        stream_id: sys::guint,
        component_id: sys::guint,
        ctx: &GMainContext,
        f: F,
    ) -> BoolResult<()> {
        extern "C" fn wrapper<F: FnMut(&[u8]) + Send + 'static>(
            _agent: *mut sys::NiceAgent,
            _stream_id: sys::guint,
            _component_id: sys::guint,
            len: sys::guint,
            buf: *mut sys::gchar,
            user_data: sys::gpointer,
        ) {
            let f_ptr = user_data as *mut F;
            let f = unsafe { &mut *f_ptr };
            let buf = unsafe { std::slice::from_raw_parts(buf as *mut u8, len as usize) };
            f(buf)
        }
        let mut boxed_f = Box::new(f);
        let res = unsafe {
            sys::nice_agent_attach_recv(
                self.ptr,
                stream_id,
                component_id,
                ctx.0,
                Some(wrapper::<F>),
                boxed_f.deref_mut() as *mut F as sys::gpointer,
            )
        };
        if res < 0 {
            return Err("attach_recv failed");
        }
        self.recv_callbacks
            .insert((stream_id, component_id), boxed_f);
        Ok(())
    }

    /// Detaches a callback attached with [NiceAgent::attach_recv].
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-attach-recv
    pub fn detach_recv<F: FnMut(&[u8]) + Send + 'static>(
        &mut self,
        stream_id: sys::guint,
        component_id: sys::guint,
        ctx: &GMainContext,
    ) -> BoolResult<()> {
        let res = unsafe {
            sys::nice_agent_attach_recv(
                self.ptr,
                stream_id,
                component_id,
                ctx.0,
                None,
                ptr::null_mut(),
            )
        };
        if res < 0 {
            return Err("attach_recv failed");
        }
        self.recv_callbacks.remove(&(stream_id, component_id));
        Ok(())
    }
}

impl Drop for NiceAgent {
    fn drop(&mut self) {
        unsafe {
            sys::g_object_unref(self.ptr as sys::gpointer);
        }
    }
}

foreign_type! {
    type CType = sys::NiceCandidate;
    fn drop = sys::nice_candidate_free;
    fn clone = sys::nice_candidate_copy;
    /// See the [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceCandidate.html
    pub struct NiceCandidate;
    /// Reference to [NiceCandidate].
    pub struct NiceCandidateRef;
}

impl NiceCandidate {
    /// Creates a new NiceCandidate.
    pub fn new(type_: NiceCandidateType) -> Self {
        Self(unsafe { sys::nice_candidate_new(type_ as u32) })
    }

    // FIXME this should probably return a result instead of unwrapping internally
    /// Creates a new NiceCandidate from an [SdpAttributeCandidate].
    pub fn from_sdp(sdp: &SdpAttributeCandidate) -> Self {
        let mut raw = Self::new(match sdp.c_type {
            SdpAttributeCandidateType::Host => NiceCandidateType::Host,
            SdpAttributeCandidateType::Srflx => NiceCandidateType::ServerReflexive,
            SdpAttributeCandidateType::Prflx => NiceCandidateType::PeerReflexive,
            SdpAttributeCandidateType::Relay => NiceCandidateType::Relayed,
        });
        raw.set_transport(match sdp.transport {
            SdpAttributeCandidateTransport::Udp => NiceCandidateTransport::Udp,
            SdpAttributeCandidateTransport::Tcp => match sdp
                .tcp_type
                .as_ref()
                .expect("transport is tcp but tcp_type is not set")
            {
                SdpAttributeCandidateTcpType::Active => NiceCandidateTransport::TcpActive,
                SdpAttributeCandidateTcpType::Passive => NiceCandidateTransport::TcpPassive,
                SdpAttributeCandidateTcpType::Simultaneous => NiceCandidateTransport::TcpSO,
            },
        });
        raw.set_addr(SocketAddr::new(sdp.address, sdp.port as u16));
        raw.set_priority(sdp.priority as u32); // FIXME check for oob
        raw.set_component_id(sdp.component as sys::guint);
        raw.set_foundation(&CString::new(sdp.foundation.clone()).unwrap());
        raw
    }
}

impl NiceCandidateRef {
    /// Returns the `stream_id` field.
    pub fn stream_id(&self) -> sys::guint {
        let raw = unsafe { &*self.as_ptr() };
        raw.stream_id
    }

    /// Returns the `type` field.
    pub fn type_(&self) -> NiceCandidateType {
        let raw = unsafe { &*self.as_ptr() };
        raw.type_.into()
    }

    /// Returns the `transport` field.
    pub fn transport(&self) -> NiceCandidateTransport {
        let raw = unsafe { &*self.as_ptr() };
        raw.transport.into()
    }

    /// Sets the `transport` field.
    pub fn set_transport(&mut self, transport: NiceCandidateTransport) {
        let raw = unsafe { &mut *self.as_ptr() };
        raw.transport = transport as u32;
    }

    /// Returns the `addr` field.
    pub fn addr(&self) -> SocketAddr {
        let raw = unsafe { &*self.as_ptr() };
        from_nice_addr(raw.addr)
    }

    /// Sets the `addr` field.
    pub fn set_addr(&mut self, addr: impl Borrow<SocketAddr>) {
        let raw = unsafe { &mut *self.as_ptr() };
        to_nice_addr(addr.borrow(), &mut raw.addr);
    }

    /// Returns the `priority` field.
    pub fn priority(&self) -> u32 {
        let raw = unsafe { &*self.as_ptr() };
        raw.priority
    }

    /// Sets the `priority` field.
    pub fn set_priority(&mut self, priority: u32) {
        let raw = unsafe { &mut *self.as_ptr() };
        raw.priority = priority;
    }

    /// Returns the `component_id` field.
    pub fn component_id(&self) -> sys::guint {
        let raw = unsafe { &*self.as_ptr() };
        raw.component_id
    }

    /// Sets the `component_id` field.
    pub fn set_component_id(&mut self, component_id: sys::guint) {
        let raw = unsafe { &mut *self.as_ptr() };
        raw.component_id = component_id;
    }

    /// Returns the `foundation` field.
    pub fn foundation(&self) -> &CStr {
        let raw = unsafe { &*self.as_ptr() };
        unsafe { CStr::from_ptr((&raw.foundation) as *const c_char) }
    }

    /// Sets the `foundation` field.
    ///
    /// **Note**: Panics if the supplied foundation is longer than
    ///           [sys::NICE_CANDIDATE_MAX_FOUNDATION].
    pub fn set_foundation(&mut self, foundation: &CStr) {
        let self_foundation = unsafe { &mut (*self.as_ptr()).foundation };
        let foundation = foundation.to_bytes_with_nul();
        if foundation.len() > self_foundation.len() {
            panic!("foundation too long (>{} bytes)", self_foundation.len());
        }
        for i in 0..foundation.len() {
            self_foundation[i] = foundation[i] as i8;
        }
    }

    /// Converts this candidate into an [SdpAttributeCandidate].
    pub fn to_sdp(&self) -> SdpAttributeCandidate {
        let address = self.addr();
        SdpAttributeCandidate {
            foundation: self
                .foundation()
                .to_owned()
                .into_string()
                .expect("foundation is ascii"),
            component: self.component_id() as u32,
            transport: match self.transport() {
                NiceCandidateTransport::Udp => SdpAttributeCandidateTransport::Udp,
                _ => SdpAttributeCandidateTransport::Tcp,
            },
            priority: u64::from(self.priority()),
            address: address.ip(),
            port: u32::from(address.port()),
            c_type: match self.type_() {
                NiceCandidateType::Host => SdpAttributeCandidateType::Host,
                NiceCandidateType::ServerReflexive => SdpAttributeCandidateType::Srflx,
                NiceCandidateType::PeerReflexive => SdpAttributeCandidateType::Prflx,
                NiceCandidateType::Relayed => SdpAttributeCandidateType::Relay,
            },
            raddr: None,
            rport: None,
            tcp_type: match self.transport() {
                NiceCandidateTransport::Udp => None,
                NiceCandidateTransport::TcpActive => Some(SdpAttributeCandidateTcpType::Active),
                NiceCandidateTransport::TcpPassive => Some(SdpAttributeCandidateTcpType::Passive),
                NiceCandidateTransport::TcpSO => Some(SdpAttributeCandidateTcpType::Simultaneous),
            },
            generation: None,
            ufrag: None,
            networkcost: None,
            unknown_extensions: Vec::new(),
        }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceCandidate.html#NiceCandidateType
#[allow(missing_docs)] // see libnice docs
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NiceCandidateType {
    Host = sys::NiceCandidateType_NICE_CANDIDATE_TYPE_HOST as isize,
    ServerReflexive = sys::NiceCandidateType_NICE_CANDIDATE_TYPE_SERVER_REFLEXIVE as isize,
    PeerReflexive = sys::NiceCandidateType_NICE_CANDIDATE_TYPE_PEER_REFLEXIVE as isize,
    Relayed = sys::NiceCandidateType_NICE_CANDIDATE_TYPE_RELAYED as isize,
}

impl From<sys::NiceCandidateType> for NiceCandidateType {
    fn from(raw: sys::NiceCandidateType) -> Self {
        match raw {
            sys::NiceCandidateType_NICE_CANDIDATE_TYPE_HOST => NiceCandidateType::Host,
            sys::NiceCandidateType_NICE_CANDIDATE_TYPE_SERVER_REFLEXIVE => {
                NiceCandidateType::ServerReflexive
            }
            sys::NiceCandidateType_NICE_CANDIDATE_TYPE_PEER_REFLEXIVE => {
                NiceCandidateType::PeerReflexive
            }
            sys::NiceCandidateType_NICE_CANDIDATE_TYPE_RELAYED => NiceCandidateType::Relayed,
            _ => panic!("unknown NiceCandidateType: {}", raw),
        }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceCandidate.html#NiceCandidateTransport
#[allow(missing_docs)] // see libnice docs
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NiceCandidateTransport {
    Udp = sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_UDP as isize,
    TcpActive = sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_ACTIVE as isize,
    TcpPassive = sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_PASSIVE as isize,
    TcpSO = sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_SO as isize,
}

impl From<sys::NiceCandidateTransport> for NiceCandidateTransport {
    fn from(raw: sys::NiceCandidateTransport) -> Self {
        match raw {
            sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_UDP => NiceCandidateTransport::Udp,
            sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_ACTIVE => {
                NiceCandidateTransport::TcpActive
            }
            sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_PASSIVE => {
                NiceCandidateTransport::TcpPassive
            }
            sys::NiceCandidateTransport_NICE_CANDIDATE_TRANSPORT_TCP_SO => {
                NiceCandidateTransport::TcpSO
            }
            _ => panic!("unknown NiceCandidateTransport: {}", raw),
        }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceCandidate.html#NiceRelayType
#[allow(missing_docs)] // see libnice docs
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NiceRelayType {
    TurnUdp = sys::NiceRelayType_NICE_RELAY_TYPE_TURN_UDP as isize,
    TurnTcp = sys::NiceRelayType_NICE_RELAY_TYPE_TURN_TCP as isize,
    TurnTls = sys::NiceRelayType_NICE_RELAY_TYPE_TURN_TLS as isize,
}

impl From<sys::NiceRelayType> for NiceRelayType {
    fn from(raw: sys::NiceRelayType) -> Self {
        match raw {
            sys::NiceRelayType_NICE_RELAY_TYPE_TURN_UDP => NiceRelayType::TurnUdp,
            sys::NiceRelayType_NICE_RELAY_TYPE_TURN_TCP => NiceRelayType::TurnTcp,
            sys::NiceRelayType_NICE_RELAY_TYPE_TURN_TLS => NiceRelayType::TurnTls,
            _ => panic!("unknown NiceRelayType: {}", raw),
        }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#NiceComponentState
#[allow(missing_docs)] // see libnice docs
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NiceComponentState {
    Disconnected = sys::NiceComponentState_NICE_COMPONENT_STATE_DISCONNECTED as isize,
    Gathering = sys::NiceComponentState_NICE_COMPONENT_STATE_GATHERING as isize,
    Connecting = sys::NiceComponentState_NICE_COMPONENT_STATE_CONNECTING as isize,
    Connected = sys::NiceComponentState_NICE_COMPONENT_STATE_CONNECTED as isize,
    Ready = sys::NiceComponentState_NICE_COMPONENT_STATE_READY as isize,
    Failed = sys::NiceComponentState_NICE_COMPONENT_STATE_FAILED as isize,
}

impl From<sys::NiceComponentState> for NiceComponentState {
    fn from(raw: sys::NiceComponentState) -> Self {
        use NiceComponentState::*;
        match raw {
            sys::NiceComponentState_NICE_COMPONENT_STATE_DISCONNECTED => Disconnected,
            sys::NiceComponentState_NICE_COMPONENT_STATE_GATHERING => Gathering,
            sys::NiceComponentState_NICE_COMPONENT_STATE_CONNECTING => Connecting,
            sys::NiceComponentState_NICE_COMPONENT_STATE_CONNECTED => Connected,
            sys::NiceComponentState_NICE_COMPONENT_STATE_READY => Ready,
            sys::NiceComponentState_NICE_COMPONENT_STATE_FAILED => Failed,
            _ => panic!("unknown NiceComponentState: {}", raw),
        }
    }
}

/// See the [libnice] documentation.
///
/// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#NiceCompatibility
#[allow(missing_docs)] // see libnice docs
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NiceCompatibility {
    RFC5245 = sys::NiceCompatibility_NICE_COMPATIBILITY_RFC5245 as isize,
    GOOGLE = sys::NiceCompatibility_NICE_COMPATIBILITY_GOOGLE as isize,
    MSN = sys::NiceCompatibility_NICE_COMPATIBILITY_MSN as isize,
    WLM2009 = sys::NiceCompatibility_NICE_COMPATIBILITY_WLM2009 as isize,
    OC2007 = sys::NiceCompatibility_NICE_COMPATIBILITY_OC2007 as isize,
    OC2007R2 = sys::NiceCompatibility_NICE_COMPATIBILITY_OC2007R2 as isize,
}

fn from_nice_addr(raw: sys::NiceAddress) -> SocketAddr {
    unsafe {
        match u32::from(raw.s.addr.sa_family) {
            sys::AF_INET => (
                Ipv4Addr::from(u32::from_be(raw.s.ip4.sin_addr.s_addr)),
                u16::from_be(raw.s.ip4.sin_port),
            )
                .into(),
            sys::AF_INET6 => (
                Ipv6Addr::from(raw.s.ip6.sin6_addr.__in6_u.__u6_addr8),
                u16::from_be(raw.s.ip4.sin_port),
            )
                .into(),
            other => panic!("unknown AF type: {}", other),
        }
    }
}

fn to_nice_addr(addr: &SocketAddr, raw: &mut sys::NiceAddress) {
    match addr {
        SocketAddr::V4(addr) => unsafe {
            raw.s.ip4.sin_family = sys::AF_INET as u16;
            raw.s.ip4.sin_port = addr.port().to_be();
            raw.s.ip4.sin_addr.s_addr = u32::from(*addr.ip()).to_be();
        },
        SocketAddr::V6(addr) => unsafe {
            raw.s.ip6.sin6_family = sys::AF_INET6 as u16;
            raw.s.ip6.sin6_port = addr.port().to_be();
            raw.s.ip6.sin6_addr.__in6_u.__u6_addr8 = addr.ip().octets();
        },
    }
}

const G_TYPE_BOOLEAN: sys::GType = 5 << sys::G_TYPE_FUNDAMENTAL_SHIFT;

/// Creates a new [sys::GValue] of the specified type, containing the default value for that type.
/// # Safety
/// `type_` must be valid. This cannot be an enum since glib supports dynamic type registration.
pub unsafe fn new_g_value(type_: sys::GType) -> sys::GValue {
    let mut value = std::mem::zeroed::<sys::GValue>();
    sys::g_value_init(&mut value, type_);
    value
}
