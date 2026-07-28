//! Signal plumbing (spec section 8).
//!
//! `SIGINT`  — stop cleanly, checkpoint, print a final summary, exit UNKNOWN.
//! `SIGUSR1` — dump a stats snapshot immediately without stopping.
//!
//! The registration itself needs `signal-hook`, which is not one of the four
//! dependencies the spec authorises, so it lives behind the optional `signals`
//! feature. The flags below exist unconditionally, so the solver's clean-stop
//! path is always compiled and always testable; without the feature nothing
//! ever sets them from a signal.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[derive(Clone, Default)]
pub struct Interrupt {
    stop: Arc<AtomicBool>,
    dump: Arc<AtomicBool>,
}

impl Interrupt {
    pub fn new() -> Interrupt {
        Interrupt::default()
    }

    /// Register OS handlers. A no-op unless built with `--features signals`
    /// on a Unix target.
    pub fn install(&self) -> anyhow::Result<()> {
        #[cfg(all(feature = "signals", unix))]
        {
            signal_hook::flag::register(signal_hook::consts::SIGINT, self.stop.clone())?;
            signal_hook::flag::register(signal_hook::consts::SIGTERM, self.stop.clone())?;
            signal_hook::flag::register(signal_hook::consts::SIGUSR1, self.dump.clone())?;
        }
        Ok(())
    }

    #[inline]
    pub fn stop_requested(&self) -> bool {
        self.stop.load(Ordering::Relaxed)
    }

    /// Consume a pending dump request.
    #[inline]
    pub fn take_dump(&self) -> bool {
        self.dump.swap(false, Ordering::Relaxed)
    }

    /// Programmatic equivalents of the two signals, so the clean-stop path is
    /// exercisable on platforms where the signals do not exist.
    #[allow(dead_code)]
    pub fn request_stop(&self) {
        self.stop.store(true, Ordering::Relaxed);
    }

    #[allow(dead_code)]
    pub fn request_dump(&self) {
        self.dump.store(true, Ordering::Relaxed);
    }
}

/// Whether OS signal handling is actually compiled in.
pub const SIGNALS_AVAILABLE: bool = cfg!(all(feature = "signals", unix));
