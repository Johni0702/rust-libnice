#![allow(clippy::ptr_offset_with_cast)] // glib_wrapper emits these
use glib::BoolError;
use glib::MainContext;
use glib::ObjectExt;
use glib::SignalHandlerId;
use std::borrow::Borrow;
use std::ffi::CStr;
use std::ffi::CString;
use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::SocketAddr;
use std::ops::DerefMut;
use std::os::raw::c_char;
use std::os::raw::c_uint;
use webrtc_sdp::attribute_type::SdpAttributeCandidate;
use webrtc_sdp::attribute_type::SdpAttributeCandidateTcpType;
use webrtc_sdp::attribute_type::SdpAttributeCandidateTransport;
use webrtc_sdp::attribute_type::SdpAttributeCandidateType;

// Need these for https://github.com/gtk-rs/glib/issues/420f
use glib::translate::*;
use glib_sys as glib_ffi;
use gobject_sys as gobject_ffi;
use std::mem;
use std::ptr;

use libnice_sys as sys;

glib_wrapper! {
    /// See the [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html
    pub struct NiceAgent(Object<sys::NiceAgent>);

    match fn {
        get_type => || sys::nice_agent_get_type(),
    }
}

unsafe impl Send for NiceAgent {}
unsafe impl Sync for NiceAgent {}

/// Either `Ok(T)` or `Err` with a string description of the function that failed.
///
/// Many libnice functions only return a single boolean to indicate failure. This Result type
/// is used for such functions where no better alternative exists.
pub type BoolResult<T> = Result<T, BoolError>;

impl NiceAgent {
    /// Creates a new NiceAgent in RFC5245 compatibility mode.
    pub fn new_rfc5245(ctx: &MainContext) -> NiceAgent {
        Self::new(ctx, NiceCompatibility::RFC5245)
    }

    /// Creates a new NiceAgent with the specified compatibility mode.
    pub fn new(ctx: &MainContext, compat: NiceCompatibility) -> NiceAgent {
        let ptr = unsafe { sys::nice_agent_new(ctx.to_glib_none().0, compat as u32) };
        if ptr.is_null() {
            panic!("nice_agent_new failed");
        }
        unsafe { NiceAgent::from_glib_full(ptr) }
    }

    /// Attaches a callback function to the `new-candidate-full` signal.
    pub fn on_new_candidate<F: Fn(&NiceCandidate) + Send + Sync + 'static>(
        &mut self,
        f: F,
    ) -> BoolResult<SignalHandlerId> {
        self.connect("new-candidate-full", false, move |values| {
            f(&values[1].get().unwrap());
            None
        })
    }

    /// Attaches a callback function to the `candidate-gathering-done` signal.
    pub fn on_candidate_gathering_done<F: Fn(c_uint) + Send + Sync + 'static>(
        &mut self,
        f: F,
    ) -> BoolResult<SignalHandlerId> {
        self.connect("candidate-gathering-done", false, move |values| {
            f(values[1].get().unwrap());
            None
        })
    }

    /// Attaches a callback function to the `component-state-changed` signal.
    pub fn on_component_state_changed<F>(&mut self, f: F) -> BoolResult<SignalHandlerId>
    where
        F: Fn(c_uint, c_uint, NiceComponentState) + Send + Sync + 'static,
    {
        self.connect("component-state-changed", false, move |values| {
            let stream_id = values[1].get().unwrap();
            let component_id = values[2].get().unwrap();
            let state: c_uint = values[3].get().unwrap();
            f(stream_id, component_id, state.into());
            None
        })
    }

    /// See the [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-software
    pub fn set_software(&self, name: impl Borrow<CStr>) {
        unsafe { sys::nice_agent_set_software(self.to_glib_none().0, name.borrow().as_ptr()) }
    }

    /// Changes whether this agent is in controlling mode (by default it is not).
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#NiceAgent--controlling-mode
    pub fn set_controlling_mode(&mut self, controlling: bool) {
        self.set_property("controlling-mode", &controlling)
            .expect("failed to set controlling-mode property");
    }

    /// Adds a new stream to this agent and returns its id.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-add-stream
    pub fn add_stream(&self, components: c_uint) -> BoolResult<c_uint> {
        let id = unsafe { sys::nice_agent_add_stream(self.to_glib_none().0, components) };
        if id == 0 {
            return Err(BoolError("add_stream failed"));
        }
        Ok(id)
    }

    /// Starts candidate gathering for a stream.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-gather-candidates
    pub fn gather_candidates(&self, stream_id: c_uint) -> BoolResult<()> {
        BoolError::from_glib(
            unsafe { sys::nice_agent_gather_candidates(self.to_glib_none().0, stream_id) },
            "gather_candidates failed",
        )
    }

    /// Sets the remote ICE credentials for a stream.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-remote-credentials
    pub fn set_remote_credentials(
        &self,
        stream_id: c_uint,
        ufrag: &CStr,
        pwd: &CStr,
    ) -> BoolResult<()> {
        BoolError::from_glib(
            unsafe {
                sys::nice_agent_set_remote_credentials(
                    self.to_glib_none().0,
                    stream_id,
                    ufrag.as_ptr(),
                    pwd.as_ptr(),
                )
            },
            "set_remote_credentials failed",
        )
    }

    /// Returns the local ICE credentials as `(ufrag, pwd)`.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-get-local-credentials
    pub fn get_local_credentials(&self, stream_id: c_uint) -> BoolResult<(CString, CString)> {
        let mut ufrag_ptr: *mut c_char = ptr::null_mut();
        let mut pwd_ptr: *mut c_char = ptr::null_mut();
        if unsafe {
            sys::nice_agent_get_local_credentials(
                self.to_glib_none().0,
                stream_id,
                &mut ufrag_ptr,
                &mut pwd_ptr,
            )
        } == 0
        {
            return Err(BoolError("set_remote_credentials failed"));
        }
        let ufrag = unsafe { CStr::from_ptr(ufrag_ptr) }.to_owned();
        let pwd = unsafe { CStr::from_ptr(pwd_ptr) }.to_owned();
        unsafe {
            glib_sys::g_free(ufrag_ptr as glib_sys::gpointer);
            glib_sys::g_free(pwd_ptr as glib_sys::gpointer);
        }
        Ok((ufrag, pwd))
    }

    /// Adds a remote ICE candidate for a particular stream component.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-set-remote-candidates
    pub fn add_remote_candidates<'a>(
        &self,
        stream_id: c_uint,
        component_id: c_uint,
        candidates: &'a [&'a NiceCandidate],
    ) -> BoolResult<usize> {
        // FIXME what does this function actually do? the docs talk about add but its name says set
        let res = unsafe {
            let mut list = ptr::null_mut::<glib_sys::GSList>();
            for candidate in candidates.iter().rev() {
                list = glib_sys::g_slist_prepend(list, Ptr::to(candidate.to_glib_none().0));
            }
            let res = sys::nice_agent_set_remote_candidates(
                self.to_glib_none().0,
                stream_id,
                component_id,
                /*
                list_entries
                    .last()
                    .map_or_else(ptr::null, |head| head as *const sys::GSList),
                */
                list,
            );
            glib_sys::g_slist_free(list);
            res
        };
        if res < 0 {
            return Err(BoolError("set_remote_candidates failed"));
        }
        Ok(res as usize)
    }

    /// Limits the range of ports used for host candidates.
    /// If this agent has exhausted the specified range, [NiceAgent::gather_candidates] will fail.
    /// Must be called before [NiceAgent::gather_candidates].
    pub fn set_port_range(
        &self,
        stream_id: c_uint,
        component_id: c_uint,
        min_port: u16,
        max_port: u16,
    ) {
        unsafe {
            sys::nice_agent_set_port_range(
                self.to_glib_none().0,
                stream_id,
                component_id,
                min_port.into(),
                max_port.into(),
            )
        }
    }

    /// Sends data via the specified stream component.
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-send
    pub fn send(&self, stream_id: c_uint, component_id: c_uint, buf: &[u8]) -> Option<usize> {
        let res = unsafe {
            sys::nice_agent_send(
                self.to_glib_none().0,
                stream_id,
                component_id,
                buf.len() as c_uint,
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
    ///
    /// The active callback is detached when the returned handle is dropped.
    /// Since there's no way to query the current callback, any callback for the component is
    /// detached when the handle is dropped, even if the one corresponding to the handle has already
    /// be replaced by a new one.
    /// Therefore, if you wish to replace the current callback, you must first drop the old handle
    /// and only then attach a new callback.
    pub fn attach_recv<F: FnMut(&[u8]) + Send + 'static>(
        &mut self,
        stream_id: c_uint,
        component_id: c_uint,
        ctx: &MainContext,
        f: F,
    ) -> BoolResult<AttachRecvHandle> {
        extern "C" fn wrapper<F: FnMut(&[u8]) + Send + 'static>(
            _agent: *mut sys::NiceAgent,
            _stream_id: c_uint,
            _component_id: c_uint,
            len: c_uint,
            buf: *mut c_char,
            user_data: glib_sys::gpointer,
        ) {
            let f_ptr = user_data as *mut F;
            let f = unsafe { &mut *f_ptr };
            let buf = unsafe { std::slice::from_raw_parts(buf as *mut u8, len as usize) };
            f(buf)
        }
        let mut boxed_f = Box::new(f);
        let res = unsafe {
            sys::nice_agent_attach_recv(
                self.to_glib_none().0,
                stream_id,
                component_id,
                ctx.to_glib_none().0,
                Some(wrapper::<F>),
                boxed_f.deref_mut() as *mut F as glib_sys::gpointer,
            )
        };
        if res < 0 {
            return Err(BoolError("attach_recv failed"));
        }
        Ok(AttachRecvHandle(
            self.clone(),
            stream_id,
            component_id,
            ctx.clone(),
            boxed_f,
        ))
    }

    /// Detaches a callback attached with [NiceAgent::attach_recv].
    /// [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceAgent.html#nice-agent-attach-recv
    ///
    /// Note that the callback itself is only dropped once the handle returned from
    /// [NiceAgent::attach_recv] is dropped.
    pub fn detach_recv(
        &mut self,
        stream_id: c_uint,
        component_id: c_uint,
        ctx: &MainContext,
    ) -> BoolResult<()> {
        let res = unsafe {
            sys::nice_agent_attach_recv(
                self.to_glib_none().0,
                stream_id,
                component_id,
                ctx.to_glib_none().0,
                None,
                ptr::null_mut(),
            )
        };
        if res < 0 {
            return Err(BoolError("attach_recv failed"));
        }
        Ok(())
    }
}

/// Handle keeping a callback alive which was previously attached with [NiceAgent::attach_recv].
///
/// Dropping this handle will detach **any** currently attached callback for the same component.
#[must_use = "when an AttachRecvHandle is dropped, it detaches the callback"]
pub struct AttachRecvHandle(NiceAgent, c_uint, c_uint, MainContext, Box<dyn std::any::Any + Send>);

impl Drop for AttachRecvHandle {
    fn drop(&mut self) {
        self.0
            .detach_recv(self.1, self.2, &self.3)
            .expect("cannot continue safely when detach failed");
    }
}

glib_wrapper! {
    /// See the [libnice] documentation.
    ///
    /// [libnice]: https://nice.freedesktop.org/libnice/NiceCandidate.html
    pub struct NiceCandidate(Boxed<sys::NiceCandidate>);

    match fn {
        copy => |ptr| sys::nice_candidate_copy(ptr),
        free => |ptr| sys::nice_candidate_free(ptr),
        // Cannot use the obvious solution as it is only available in the latest release
        // which will take some time to be distributed everywhere
        // get_type => || sys::nice_candidate_get_type(),
        get_type => || glib::Type::from_name("NiceCandidate").unwrap().to_glib(),
    }
}

impl NiceCandidate {
    /// Creates a new NiceCandidate.
    pub fn new(type_: NiceCandidateType) -> Self {
        unsafe { Self::from_glib_full(sys::nice_candidate_new(type_ as u32)) }
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
        raw.set_component_id(sdp.component as c_uint);
        raw.set_foundation(&CString::new(sdp.foundation.clone()).unwrap());
        raw
    }

    /// Returns the `stream_id` field.
    pub fn stream_id(&self) -> c_uint {
        let raw = unsafe { &*self.to_glib_none().0 };
        raw.stream_id
    }

    /// Returns the `type` field.
    pub fn type_(&self) -> NiceCandidateType {
        let raw = unsafe { &*self.to_glib_none().0 };
        raw.type_.into()
    }

    /// Returns the `transport` field.
    pub fn transport(&self) -> NiceCandidateTransport {
        let raw = unsafe { &*self.to_glib_none().0 };
        raw.transport.into()
    }

    /// Sets the `transport` field.
    pub fn set_transport(&mut self, transport: NiceCandidateTransport) {
        let raw = unsafe { &mut *self.to_glib_none_mut().0 };
        raw.transport = transport as u32;
    }

    /// Returns the `addr` field.
    pub fn addr(&self) -> SocketAddr {
        let raw = unsafe { &*self.to_glib_none().0 };
        from_nice_addr(&raw.addr)
    }

    /// Sets the `addr` field.
    pub fn set_addr(&mut self, addr: impl Borrow<SocketAddr>) {
        let raw = unsafe { &mut *self.to_glib_none_mut().0 };
        to_nice_addr(addr.borrow(), &mut raw.addr);
    }

    /// Returns the `priority` field.
    pub fn priority(&self) -> u32 {
        let raw = unsafe { &*self.to_glib_none().0 };
        raw.priority
    }

    /// Sets the `priority` field.
    pub fn set_priority(&mut self, priority: u32) {
        let raw = unsafe { &mut *self.to_glib_none_mut().0 };
        raw.priority = priority;
    }

    /// Returns the `component_id` field.
    pub fn component_id(&self) -> c_uint {
        let raw = unsafe { &*self.to_glib_none().0 };
        raw.component_id
    }

    /// Sets the `component_id` field.
    pub fn set_component_id(&mut self, component_id: c_uint) {
        let raw = unsafe { &mut *self.to_glib_none_mut().0 };
        raw.component_id = component_id;
    }

    /// Returns the `foundation` field.
    pub fn foundation(&self) -> &CStr {
        let raw = unsafe { &*self.to_glib_none().0 };
        unsafe { CStr::from_ptr((&raw.foundation) as *const c_char) }
    }

    /// Sets the `foundation` field.
    ///
    /// **Note**: Panics if the supplied foundation is longer than 32 bytes.
    pub fn set_foundation(&mut self, foundation: &CStr) {
        let self_foundation = unsafe { &mut (*self.to_glib_none_mut().0).foundation };
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

fn from_nice_addr(raw: &sys::NiceAddress) -> SocketAddr {
    unsafe {
        match i32::from(raw.s.addr.sa_family) {
            libc::AF_INET => (
                Ipv4Addr::from(u32::from_be(raw.s.ip4.sin_addr.s_addr)),
                u16::from_be(raw.s.ip4.sin_port),
            )
                .into(),
            libc::AF_INET6 => (
                Ipv6Addr::from(raw.s.ip6.sin6_addr.s6_addr),
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
            raw.s.ip4.sin_family = libc::AF_INET as u16;
            raw.s.ip4.sin_port = addr.port().to_be();
            raw.s.ip4.sin_addr.s_addr = u32::from(*addr.ip()).to_be();
        },
        SocketAddr::V6(addr) => unsafe {
            raw.s.ip6.sin6_family = libc::AF_INET6 as u16;
            raw.s.ip6.sin6_port = addr.port().to_be();
            raw.s.ip6.sin6_addr.s6_addr = addr.ip().octets();
        },
    }
}
