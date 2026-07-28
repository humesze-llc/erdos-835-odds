/* C bridge from Rust to CaDiCaL's IPASIR-UP `ExternalPropagator`.
 *
 * CaDiCaL's own C API (`ccadical.h`) stops at plain IPASIR: it exposes no way
 * to attach a user propagator.  This header is the missing surface -- a vtable
 * of plain function pointers plus an opaque context, which is the shape Rust
 * can hand across FFI.
 *
 * Callback contract mirrors `CaDiCaL::ExternalPropagator` one-to-one; see
 * vendor/cadical/src/cadical.hpp around line 1163 for the normative comments.
 * Booleans cross as `int` (0 = false).
 */
#ifndef S45_SHIM_H
#define S45_SHIM_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct S45Callbacks {
  /* Observed-variable assignments, possibly batched. */
  void (*notify_assignment) (void *ctx, const int *lits, size_t n);
  void (*notify_new_decision_level) (void *ctx);
  void (*notify_backtrack) (void *ctx, size_t new_level);

  /* Final check on a complete assignment; 0 => provide a clause next. */
  int (*cb_check_found_model) (void *ctx, const int *model, size_t n);

  /* 0 => let the solver pick. */
  int (*cb_decide) (void *ctx);

  /* Next theory-propagated literal, or 0. */
  int (*cb_propagate) (void *ctx);

  /* Reason clause for a literal previously returned by cb_propagate,
   * streamed literal-by-literal and terminated by 0. */
  int (*cb_add_reason_clause_lit) (void *ctx, int propagated_lit);

  /* 1 => a clause is pending; *is_forgettable set by the callee. */
  int (*cb_has_external_clause) (void *ctx, int *is_forgettable);
  int (*cb_add_external_clause_lit) (void *ctx);
} S45Callbacks;

typedef struct S45Solver S45Solver;

S45Solver *s45_new (void);
void s45_delete (S45Solver *);

/* Attach the propagator.  `ctx` is passed back verbatim to every callback and
 * is never dereferenced on this side. */
void s45_connect (S45Solver *, const S45Callbacks *, void *ctx,
                  int is_lazy, int reasons_forgettable);
void s45_disconnect (S45Solver *);

void s45_add_observed_var (S45Solver *, int var);
void s45_add (S45Solver *, int lit);
void s45_reserve (S45Solver *, int max_var);
int s45_set_option (S45Solver *, const char *name, int val);
int s45_set_limit (S45Solver *, const char *name, int val);
void s45_phase (S45Solver *, int lit);

int s45_solve (S45Solver *);
int s45_val (S45Solver *, int lit);
int s45_fixed (S45Solver *, int lit);
void s45_print_statistics (S45Solver *);
const char *s45_signature (void);

/* Terminator: Rust polls this to honour --timeout without a signal handler. */
void s45_connect_terminator (S45Solver *, int (*fn) (void *), void *ctx);

#ifdef __cplusplus
}
#endif

#endif /* S45_SHIM_H */
