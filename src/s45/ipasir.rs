//! Safe-ish Rust binding to CaDiCaL's IPASIR-UP user-propagator interface.
//!
//! This is the only module in `s45` that uses `unsafe`. Everything it does is
//! FFI plumbing: the theory lives in [`crate::cdcl`], the search lives in
//! CaDiCaL, and nothing here knows what a Steiner system is.
//!
//! Ownership rule that makes the raw context pointer sound: callbacks fire
//! *only* from inside `CaDiCaL::Solver::solve`, so [`Solver::solve_with`] takes
//! `&mut P` for exactly the span of that call and disconnects before returning.
//! No propagator reference outlives the borrow.

#![allow(unsafe_code)]

use std::ffi::{c_char, c_int, c_void, CString};

#[allow(non_camel_case_types)]
type size_t = usize;

#[repr(C)]
struct Callbacks {
    notify_assignment: unsafe extern "C" fn(*mut c_void, *const c_int, size_t),
    notify_new_decision_level: unsafe extern "C" fn(*mut c_void),
    notify_backtrack: unsafe extern "C" fn(*mut c_void, size_t),
    cb_check_found_model: unsafe extern "C" fn(*mut c_void, *const c_int, size_t) -> c_int,
    cb_decide: unsafe extern "C" fn(*mut c_void) -> c_int,
    cb_propagate: unsafe extern "C" fn(*mut c_void) -> c_int,
    cb_add_reason_clause_lit: unsafe extern "C" fn(*mut c_void, c_int) -> c_int,
    cb_has_external_clause: unsafe extern "C" fn(*mut c_void, *mut c_int) -> c_int,
    cb_add_external_clause_lit: unsafe extern "C" fn(*mut c_void) -> c_int,
}

enum RawSolver {}

extern "C" {
    fn s45_new() -> *mut RawSolver;
    fn s45_delete(s: *mut RawSolver);
    fn s45_connect(s: *mut RawSolver, cbs: *const Callbacks, ctx: *mut c_void,
                   is_lazy: c_int, reasons_forgettable: c_int);
    fn s45_disconnect(s: *mut RawSolver);
    fn s45_add_observed_var(s: *mut RawSolver, var: c_int);
    fn s45_add(s: *mut RawSolver, lit: c_int);
    fn s45_reserve(s: *mut RawSolver, max_var: c_int);
    fn s45_set_option(s: *mut RawSolver, name: *const c_char, val: c_int) -> c_int;
    fn s45_set_limit(s: *mut RawSolver, name: *const c_char, val: c_int) -> c_int;
    fn s45_phase(s: *mut RawSolver, lit: c_int);
    fn s45_solve(s: *mut RawSolver) -> c_int;
    fn s45_val(s: *mut RawSolver, lit: c_int) -> c_int;
    fn s45_print_statistics(s: *mut RawSolver);
    fn s45_signature() -> *const c_char;
    fn s45_connect_terminator(s: *mut RawSolver,
                              f: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
                              ctx: *mut c_void);
}

/// The theory side of CDCL(T).
///
/// Method contracts mirror `CaDiCaL::ExternalPropagator` (vendor/cadical/src/
/// cadical.hpp:1163). Literals are DIMACS-signed 1-based variable indices.
pub trait Propagator {
    /// Observed variables just assigned, in trail order. May be batched.
    fn notify_assignment(&mut self, lits: &[i32]);
    fn notify_new_decision_level(&mut self);
    /// Backtrack to `new_level`; the propagator must undo everything above it.
    fn notify_backtrack(&mut self, new_level: usize);

    /// Last line of defence on a complete assignment. Returning `false`
    /// obliges the propagator to supply a clause on the next callback.
    fn check_found_model(&mut self, model: &[i32]) -> bool;

    /// Next theory implication, or 0 to hand control back.
    fn propagate(&mut self) -> i32 {
        0
    }
    /// Streams the reason clause for `propagated` one literal at a time,
    /// terminated by 0. The clause must contain `propagated`.
    fn add_reason_clause_lit(&mut self, propagated: i32) -> i32 {
        let _ = propagated;
        0
    }

    /// Override the solver's decision, or 0 to let VSIDS choose.
    fn decide(&mut self) -> i32 {
        0
    }

    /// `Some(forgettable)` if a clause is pending, else `None`.
    fn has_external_clause(&mut self) -> Option<bool>;
    /// Streams the pending clause, terminated by 0.
    fn add_external_clause_lit(&mut self) -> i32;

    /// Polled by CaDiCaL's terminator; `true` stops the search with UNKNOWN.
    fn terminated(&mut self) -> bool {
        false
    }
}

/// A panic unwinding into C++ is undefined behaviour, so a propagator bug has
/// to become an abort at the boundary rather than silent corruption.
fn guard<R>(f: impl FnOnce() -> R) -> R {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(_) => {
            eprintln!("s45: propagator panicked inside CaDiCaL — aborting");
            std::process::abort();
        }
    }
}

unsafe fn lits<'a>(p: *const c_int, n: usize) -> &'a [i32] {
    if n == 0 {
        &[]
    } else {
        std::slice::from_raw_parts(p, n)
    }
}

unsafe extern "C" fn t_notify_assignment<P: Propagator>(c: *mut c_void, p: *const c_int, n: size_t) {
    let s = &mut *(c as *mut P);
    let l = lits(p, n);
    guard(|| s.notify_assignment(l))
}
unsafe extern "C" fn t_new_level<P: Propagator>(c: *mut c_void) {
    let s = &mut *(c as *mut P);
    guard(|| s.notify_new_decision_level())
}
unsafe extern "C" fn t_backtrack<P: Propagator>(c: *mut c_void, lvl: size_t) {
    let s = &mut *(c as *mut P);
    guard(|| s.notify_backtrack(lvl))
}
unsafe extern "C" fn t_check_model<P: Propagator>(c: *mut c_void, p: *const c_int, n: size_t) -> c_int {
    let s = &mut *(c as *mut P);
    let m = lits(p, n);
    guard(|| s.check_found_model(m)) as c_int
}
unsafe extern "C" fn t_decide<P: Propagator>(c: *mut c_void) -> c_int {
    let s = &mut *(c as *mut P);
    guard(|| s.decide())
}
unsafe extern "C" fn t_propagate<P: Propagator>(c: *mut c_void) -> c_int {
    let s = &mut *(c as *mut P);
    guard(|| s.propagate())
}
unsafe extern "C" fn t_reason_lit<P: Propagator>(c: *mut c_void, l: c_int) -> c_int {
    let s = &mut *(c as *mut P);
    guard(|| s.add_reason_clause_lit(l))
}
unsafe extern "C" fn t_has_clause<P: Propagator>(c: *mut c_void, forget: *mut c_int) -> c_int {
    let s = &mut *(c as *mut P);
    match guard(|| s.has_external_clause()) {
        Some(f) => {
            *forget = f as c_int;
            1
        }
        None => 0,
    }
}
unsafe extern "C" fn t_clause_lit<P: Propagator>(c: *mut c_void) -> c_int {
    let s = &mut *(c as *mut P);
    guard(|| s.add_external_clause_lit())
}
unsafe extern "C" fn t_terminate<P: Propagator>(c: *mut c_void) -> c_int {
    let s = &mut *(c as *mut P);
    guard(|| s.terminated()) as c_int
}

fn table<P: Propagator>() -> Callbacks {
    Callbacks {
        notify_assignment: t_notify_assignment::<P>,
        notify_new_decision_level: t_new_level::<P>,
        notify_backtrack: t_backtrack::<P>,
        cb_check_found_model: t_check_model::<P>,
        cb_decide: t_decide::<P>,
        cb_propagate: t_propagate::<P>,
        cb_add_reason_clause_lit: t_reason_lit::<P>,
        cb_has_external_clause: t_has_clause::<P>,
        cb_add_external_clause_lit: t_clause_lit::<P>,
    }
}

pub const SATISFIABLE: i32 = 10;
pub const UNSATISFIABLE: i32 = 20;

pub struct Solver {
    ptr: *mut RawSolver,
}

impl Solver {
    pub fn new() -> Solver {
        let ptr = unsafe { s45_new() };
        assert!(!ptr.is_null(), "CaDiCaL allocation failed");
        Solver { ptr }
    }

    pub fn signature() -> String {
        unsafe { std::ffi::CStr::from_ptr(s45_signature()) }
            .to_string_lossy()
            .into_owned()
    }

    pub fn set_option(&mut self, name: &str, val: i32) -> bool {
        let c = CString::new(name).expect("option name");
        unsafe { s45_set_option(self.ptr, c.as_ptr(), val) != 0 }
    }

    pub fn set_limit(&mut self, name: &str, val: i32) -> bool {
        let c = CString::new(name).expect("limit name");
        unsafe { s45_set_limit(self.ptr, c.as_ptr(), val) != 0 }
    }

    pub fn reserve(&mut self, max_var: i32) {
        unsafe { s45_reserve(self.ptr, max_var) }
    }

    pub fn add_clause(&mut self, lits: &[i32]) {
        unsafe {
            for &l in lits {
                debug_assert!(l != 0);
                s45_add(self.ptr, l);
            }
            s45_add(self.ptr, 0);
        }
    }

    pub fn phase(&mut self, lit: i32) {
        unsafe { s45_phase(self.ptr, lit) }
    }

    /// Runs the search with `p` attached, watching `observed`. Returns
    /// 10 / 20 / 0.
    ///
    /// The observed set is declared here rather than through a standalone
    /// method because `External::add_observed_var` silently *ignores* the call
    /// when no propagator is connected (external.cpp:319). Folding it into
    /// this call makes the ordering unrepresentable rather than merely
    /// documented — getting it wrong costs an assertion deep inside
    /// `external_propagate.cpp`, which is a miserable way to learn it.
    /// `reasons_forgettable` decides whether CaDiCaL may delete the reason
    /// clauses this propagator supplies. It is a real trade, not a detail:
    /// short at-most-one binaries *are* the encoding and should be kept, while
    /// long resolved explanations accumulate into a clause database that
    /// strangles BCP if they can never be reduced.
    pub fn solve_with<P: Propagator>(
        &mut self,
        p: &mut P,
        observed: &[i32],
        reasons_forgettable: bool,
    ) -> i32 {
        let cbs = table::<P>();
        let ctx = p as *mut P as *mut c_void;
        unsafe {
            s45_connect(self.ptr, &cbs, ctx, 0, reasons_forgettable as c_int);
            for &v in observed {
                s45_add_observed_var(self.ptr, v);
            }
            s45_connect_terminator(self.ptr, Some(t_terminate::<P>), ctx);
            let r = s45_solve(self.ptr);
            s45_connect_terminator(self.ptr, None, std::ptr::null_mut());
            s45_disconnect(self.ptr);
            r
        }
    }

    pub fn val(&mut self, lit: i32) -> i32 {
        unsafe { s45_val(self.ptr, lit) }
    }

    pub fn print_statistics(&mut self) {
        unsafe { s45_print_statistics(self.ptr) }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { s45_delete(self.ptr) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Does nothing; establishes that the vendored solver links and runs.
    struct Nop;
    impl Propagator for Nop {
        fn notify_assignment(&mut self, _: &[i32]) {}
        fn notify_new_decision_level(&mut self) {}
        fn notify_backtrack(&mut self, _: usize) {}
        fn check_found_model(&mut self, _: &[i32]) -> bool {
            true
        }
        fn has_external_clause(&mut self) -> Option<bool> {
            None
        }
        fn add_external_clause_lit(&mut self) -> i32 {
            0
        }
    }

    #[test]
    fn links_and_solves() {
        assert!(Solver::signature().contains("cadical"));
        let mut s = Solver::new();
        s.add_clause(&[1, 2]);
        s.add_clause(&[-1]);
        assert_eq!(s.solve_with(&mut Nop, &[], false), SATISFIABLE);
        assert_eq!(s.val(1), -1);
        assert_eq!(s.val(2), 2);
    }

    /// Propagates `-1` at the root with the unit reason `(-1)`. The formula
    /// then forces `2` and `-2`, so the refutation exists only because the
    /// theory spoke — this is the whole CDCL(T) loop in miniature.
    struct ForceNeg1 {
        done: bool,
        cursor: usize,
    }
    impl Propagator for ForceNeg1 {
        fn notify_assignment(&mut self, _: &[i32]) {}
        fn notify_new_decision_level(&mut self) {}
        fn notify_backtrack(&mut self, _: usize) {}
        fn check_found_model(&mut self, _: &[i32]) -> bool {
            true
        }
        fn propagate(&mut self) -> i32 {
            if self.done {
                0
            } else {
                self.done = true;
                -1
            }
        }
        fn add_reason_clause_lit(&mut self, propagated: i32) -> i32 {
            assert_eq!(propagated, -1);
            self.cursor += 1;
            if self.cursor == 1 {
                -1
            } else {
                self.cursor = 0;
                0
            }
        }
        fn has_external_clause(&mut self) -> Option<bool> {
            None
        }
        fn add_external_clause_lit(&mut self) -> i32 {
            0
        }
    }

    #[test]
    fn theory_propagation_drives_unsat() {
        let mut s = Solver::new();
        s.set_option("chrono", 0);
        s.add_clause(&[1, 2]);
        s.add_clause(&[1, -2]);
        let mut p = ForceNeg1 { done: false, cursor: 0 };
        assert_eq!(s.solve_with(&mut p, &[1, 2], false), UNSATISFIABLE);
    }

    /// Same refutation, reached through `cb_has_external_clause` instead.
    struct AssertUnit(Vec<i32>, usize);
    impl Propagator for AssertUnit {
        fn notify_assignment(&mut self, _: &[i32]) {}
        fn notify_new_decision_level(&mut self) {}
        fn notify_backtrack(&mut self, _: usize) {}
        fn check_found_model(&mut self, _: &[i32]) -> bool {
            true
        }
        fn has_external_clause(&mut self) -> Option<bool> {
            if self.0.is_empty() {
                None
            } else {
                Some(false)
            }
        }
        fn add_external_clause_lit(&mut self) -> i32 {
            if self.1 < self.0.len() {
                self.1 += 1;
                self.0[self.1 - 1]
            } else {
                self.0.clear();
                self.1 = 0;
                0
            }
        }
    }

    #[test]
    fn external_clause_drives_unsat() {
        let mut s = Solver::new();
        s.set_option("chrono", 0);
        s.add_clause(&[1, 2]);
        s.add_clause(&[1, -2]);
        let mut p = AssertUnit(vec![-1], 0);
        assert_eq!(s.solve_with(&mut p, &[1, 2], false), UNSATISFIABLE);
    }
}
