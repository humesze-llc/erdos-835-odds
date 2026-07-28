#include "s45_shim.h"

#include "cadical.hpp"

#include <cstdio>
#include <vector>

namespace {

class Bridge : public CaDiCaL::ExternalPropagator {
  S45Callbacks cb;
  void *ctx;

public:
  Bridge (const S45Callbacks *c, void *x, bool lazy, bool forgettable)
      : cb (*c), ctx (x) {
    is_lazy = lazy;
    are_reasons_forgettable = forgettable;
  }

  void notify_assignment (const std::vector<int> &lits) override {
    cb.notify_assignment (ctx, lits.data (), lits.size ());
  }
  void notify_new_decision_level () override {
    cb.notify_new_decision_level (ctx);
  }
  void notify_backtrack (size_t new_level) override {
    cb.notify_backtrack (ctx, new_level);
  }
  bool cb_check_found_model (const std::vector<int> &model) override {
    return cb.cb_check_found_model (ctx, model.data (), model.size ()) != 0;
  }
  int cb_decide () override { return cb.cb_decide (ctx); }
  int cb_propagate () override { return cb.cb_propagate (ctx); }
  int cb_add_reason_clause_lit (int propagated_lit) override {
    return cb.cb_add_reason_clause_lit (ctx, propagated_lit);
  }
  bool cb_has_external_clause (bool &is_forgettable) override {
    int f = 0;
    const int r = cb.cb_has_external_clause (ctx, &f);
    is_forgettable = (f != 0);
    return r != 0;
  }
  int cb_add_external_clause_lit () override {
    return cb.cb_add_external_clause_lit (ctx);
  }
};

class Term : public CaDiCaL::Terminator {
  int (*fn) (void *);
  void *ctx;

public:
  Term (int (*f) (void *), void *x) : fn (f), ctx (x) {}
  bool terminate () override { return fn (ctx) != 0; }
};

} // namespace

// The handle owns the solver plus whatever callback adaptors are attached, so
// Rust has a single pointer to free and no lifetime to track by hand.
struct S45Solver {
  CaDiCaL::Solver solver;
  Bridge *bridge = 0;
  Term *term = 0;
  ~S45Solver () {
    if (bridge)
      solver.disconnect_external_propagator ();
    delete bridge;
    delete term;
  }
};

extern "C" {

S45Solver *s45_new (void) { return new S45Solver (); }
void s45_delete (S45Solver *s) { delete s; }

void s45_connect (S45Solver *s, const S45Callbacks *c, void *ctx, int is_lazy,
                  int reasons_forgettable) {
  if (s->bridge) {
    s->solver.disconnect_external_propagator ();
    delete s->bridge;
  }
  s->bridge = new Bridge (c, ctx, is_lazy != 0, reasons_forgettable != 0);
  s->solver.connect_external_propagator (s->bridge);
}

void s45_disconnect (S45Solver *s) {
  if (!s->bridge)
    return;
  s->solver.disconnect_external_propagator ();
  delete s->bridge;
  s->bridge = 0;
}

void s45_add_observed_var (S45Solver *s, int var) {
  s->solver.add_observed_var (var);
}
void s45_add (S45Solver *s, int lit) { s->solver.add (lit); }
void s45_reserve (S45Solver *s, int max_var) { s->solver.reserve (max_var); }
int s45_set_option (S45Solver *s, const char *name, int val) {
  return s->solver.set (name, val) ? 1 : 0;
}
int s45_set_limit (S45Solver *s, const char *name, int val) {
  return s->solver.limit (name, val) ? 1 : 0;
}
void s45_phase (S45Solver *s, int lit) { s->solver.phase (lit); }

int s45_solve (S45Solver *s) { return s->solver.solve (); }
int s45_val (S45Solver *s, int lit) { return s->solver.val (lit); }
int s45_fixed (S45Solver *s, int lit) { return s->solver.fixed (lit); }
void s45_print_statistics (S45Solver *s) { s->solver.statistics (); }
const char *s45_signature (void) { return CaDiCaL::Solver::signature (); }

void s45_connect_terminator (S45Solver *s, int (*fn) (void *), void *ctx) {
  if (s->term) {
    s->solver.disconnect_terminator ();
    delete s->term;
    s->term = 0;
  }
  if (!fn)
    return;
  s->term = new Term (fn, ctx);
  s->solver.connect_terminator (s->term);
}

} // extern "C"
