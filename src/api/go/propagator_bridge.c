#include "z3.h"
#include "_cgo_export.h"
#include <stdint.h>

/* Bridge functions that adapt C callback signatures to exported Go functions.
 * The user context (void*) is stored/received as uintptr_t to avoid unsafe pointer
 * conversion warnings in Go. */

static void propagator_push_bridge(void* ctx, Z3_solver_callback cb) {
    goPushCb((uintptr_t)ctx, cb);
}

static void propagator_pop_bridge(void* ctx, Z3_solver_callback cb, unsigned num_scopes) {
    goPopCb((uintptr_t)ctx, cb, num_scopes);
}

static void* propagator_fresh_bridge(void* ctx, Z3_context new_context) {
    return (void*)goFreshCb((uintptr_t)ctx, new_context);
}

static void propagator_fixed_bridge(void* ctx, Z3_solver_callback cb, Z3_ast t, Z3_ast value) {
    goFixedCb((uintptr_t)ctx, cb, t, value);
}

static void propagator_eq_bridge(void* ctx, Z3_solver_callback cb, Z3_ast s, Z3_ast t) {
    goEqCb((uintptr_t)ctx, cb, s, t);
}

static void propagator_diseq_bridge(void* ctx, Z3_solver_callback cb, Z3_ast s, Z3_ast t) {
    goDiseqCb((uintptr_t)ctx, cb, s, t);
}

static void propagator_final_bridge(void* ctx, Z3_solver_callback cb) {
    goFinalCb((uintptr_t)ctx, cb);
}

static void propagator_created_bridge(void* ctx, Z3_solver_callback cb, Z3_ast t) {
    goCreatedCb((uintptr_t)ctx, cb, t);
}

static void propagator_decide_bridge(void* ctx, Z3_solver_callback cb, Z3_ast t, unsigned idx, bool phase) {
    goDecideCb((uintptr_t)ctx, cb, t, idx, phase);
}

static bool propagator_on_binding_bridge(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    return goOnBindingCb((uintptr_t)ctx, cb, q, inst);
}

static void on_clause_bridge(void* ctx, Z3_ast proof_hint, unsigned n, unsigned const* deps, Z3_ast_vector literals) {
    goOnClauseCb((uintptr_t)ctx, proof_hint, n, (unsigned*)deps, literals);
}

/* C helper functions that Go calls to register callbacks.
 * These take uintptr_t for the user context and cast it to void* internally. */

void z3go_solver_propagate_init(Z3_context ctx, Z3_solver s, uintptr_t user_ctx) {
    Z3_solver_propagate_init(ctx, s, (void*)user_ctx,
        propagator_push_bridge,
        propagator_pop_bridge,
        propagator_fresh_bridge);
}

void z3go_solver_propagate_fixed(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_fixed(ctx, s, propagator_fixed_bridge);
}

void z3go_solver_propagate_final(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_final(ctx, s, propagator_final_bridge);
}

void z3go_solver_propagate_eq(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_eq(ctx, s, propagator_eq_bridge);
}

void z3go_solver_propagate_diseq(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_diseq(ctx, s, propagator_diseq_bridge);
}

void z3go_solver_propagate_created(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_created(ctx, s, propagator_created_bridge);
}

void z3go_solver_propagate_decide(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_decide(ctx, s, propagator_decide_bridge);
}

void z3go_solver_propagate_on_binding(Z3_context ctx, Z3_solver s) {
    Z3_solver_propagate_on_binding(ctx, s, propagator_on_binding_bridge);
}

void z3go_solver_register_on_clause(Z3_context ctx, Z3_solver s, uintptr_t user_ctx) {
    Z3_solver_register_on_clause(ctx, s, (void*)user_ctx, on_clause_bridge);
}
