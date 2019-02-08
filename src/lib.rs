#![deny(missing_docs)]
//! Safe high- and low-level bindings to [libnice].
//!
//! Currently not all parts of the NiceAgent have safe bindings, they are only added as needed.
//! Similarly, no safe bindings for the StunAgent or the Pseudo TCP Socket part of libnice exist.
//!
//! If required, the low-level, unsafe, generated FFI bindings are re-exported as the [sys] module.
//!
//! [libnice]: https://nice.freedesktop.org/libnice/

#[macro_use] // need macro_use, see: https://github.com/gtk-rs/glib/issues/420
extern crate glib;

/// Low-level, unsafe FFI bindings.
pub use libnice_sys as sys;

/// Low-level but still safe FFI bindings.
pub mod ffi;

/// High-level, futures-based ICE agent.
pub mod ice;

#[cfg(test)]
mod test {}
