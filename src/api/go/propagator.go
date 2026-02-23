package z3

/*
#include "z3.h"
#include <stdint.h>

// Declarations for C helper functions defined in propagator_bridge.c
extern void z3go_solver_propagate_init(Z3_context ctx, Z3_solver s, uintptr_t user_ctx);
extern void z3go_solver_propagate_fixed(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_final(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_eq(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_diseq(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_created(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_decide(Z3_context ctx, Z3_solver s);
extern void z3go_solver_propagate_on_binding(Z3_context ctx, Z3_solver s);
extern void z3go_solver_register_on_clause(Z3_context ctx, Z3_solver s, uintptr_t user_ctx);
*/
import "C"
import (
	"runtime/cgo"
)

// UserPropagator implements a custom theory propagator for Z3.
// Embed this type and override callback methods to implement a propagator.
//
// Example usage:
//
//	type MyPropagator struct {
//	    z3.UserPropagator
//	}
//
//	func (p *MyPropagator) Push() { ... }
//	func (p *MyPropagator) Pop(n uint) { ... }
//	func (p *MyPropagator) Fresh(ctx *z3.Context) z3.UserPropagatorCallbacks { return &MyPropagator{} }
type UserPropagator struct {
	ctx    *Context
	solver *Solver
	cb     C.Z3_solver_callback // current callback context, valid only during a callback
	handle cgo.Handle           // handle for passing to C as void* context
	iface  UserPropagatorCallbacks
}

// UserPropagatorCallbacks is the interface that a user propagator must implement.
// Push, Pop, and Fresh are mandatory. The other callbacks are optional.
type UserPropagatorCallbacks interface {
	// Push is called when the solver creates a new backtracking scope.
	Push()
	// Pop is called when the solver backtracks n scopes.
	Pop(n uint)
	// Fresh is called when the solver spawns a new internal solver instance.
	// Return a propagator for the new context. The callbacks registered on the
	// original propagator will also be registered on the fresh one.
	Fresh(ctx *Context) UserPropagatorCallbacks
}

// FixedHandler is implemented by propagators that handle fixed-value assignments.
type FixedHandler interface {
	Fixed(term *Expr, value *Expr)
}

// FinalHandler is implemented by propagators that handle the final check.
// The final check is invoked when all decision variables have been assigned.
type FinalHandler interface {
	Final()
}

// EqHandler is implemented by propagators that handle expression equalities.
type EqHandler interface {
	Eq(a *Expr, b *Expr)
}

// DiseqHandler is implemented by propagators that handle expression disequalities.
type DiseqHandler interface {
	Diseq(a *Expr, b *Expr)
}

// CreatedHandler is implemented by propagators that handle term creation events.
// Terms are created when they use a function declared with PropagatorDeclare.
type CreatedHandler interface {
	Created(t *Expr)
}

// DecideHandler is implemented by propagators that handle solver decision events.
type DecideHandler interface {
	Decide(t *Expr, idx uint, phase bool)
}

// OnBindingHandler is implemented by propagators that handle quantifier binding events.
// Return false to block the instantiation.
type OnBindingHandler interface {
	OnBinding(q *Expr, inst *Expr) bool
}

// newUserPropagator creates a new UserPropagator wrapping the given callbacks.
func newUserPropagator(ctx *Context, solver *Solver, iface UserPropagatorCallbacks) *UserPropagator {
	p := &UserPropagator{
		ctx:    ctx,
		solver: solver,
		iface:  iface,
	}
	p.handle = cgo.NewHandle(p)
	C.z3go_solver_propagate_init(ctx.ptr, solver.ptr, C.uintptr_t(p.handle))
	return p
}

// Close releases the resources associated with this propagator.
// It must be called when the propagator is no longer needed.
func (p *UserPropagator) Close() {
	if p.handle != 0 {
		p.handle.Delete()
		p.handle = 0
	}
}

// RegisterFixed registers the fixed-value callback.
// The propagator's iface must implement FixedHandler.
func (p *UserPropagator) RegisterFixed() {
	C.z3go_solver_propagate_fixed(p.ctx.ptr, p.solver.ptr)
}

// RegisterFinal registers the final-check callback.
// The propagator's iface must implement FinalHandler.
func (p *UserPropagator) RegisterFinal() {
	C.z3go_solver_propagate_final(p.ctx.ptr, p.solver.ptr)
}

// RegisterEq registers the equality callback.
// The propagator's iface must implement EqHandler.
func (p *UserPropagator) RegisterEq() {
	C.z3go_solver_propagate_eq(p.ctx.ptr, p.solver.ptr)
}

// RegisterDiseq registers the disequality callback.
// The propagator's iface must implement DiseqHandler.
func (p *UserPropagator) RegisterDiseq() {
	C.z3go_solver_propagate_diseq(p.ctx.ptr, p.solver.ptr)
}

// RegisterCreated registers the term-creation callback.
// The propagator's iface must implement CreatedHandler.
func (p *UserPropagator) RegisterCreated() {
	C.z3go_solver_propagate_created(p.ctx.ptr, p.solver.ptr)
}

// RegisterDecide registers the decision callback.
// The propagator's iface must implement DecideHandler.
func (p *UserPropagator) RegisterDecide() {
	C.z3go_solver_propagate_decide(p.ctx.ptr, p.solver.ptr)
}

// RegisterOnBinding registers the quantifier-binding callback.
// The propagator's iface must implement OnBindingHandler.
func (p *UserPropagator) RegisterOnBinding() {
	C.z3go_solver_propagate_on_binding(p.ctx.ptr, p.solver.ptr)
}

// Add registers an expression for propagation.
// Only Bool and BitVector expressions can be registered.
// May be called during a callback (uses the solver callback) or outside (uses the solver directly).
func (p *UserPropagator) Add(e *Expr) {
	if p.cb != nil {
		C.Z3_solver_propagate_register_cb(p.ctx.ptr, p.cb, e.ptr)
	} else {
		C.Z3_solver_propagate_register(p.ctx.ptr, p.solver.ptr, e.ptr)
	}
}

// Consequence propagates a consequence based on fixed terms.
// fixed is the list of fixed terms used as premises.
// Returns true if the propagation was accepted.
func (p *UserPropagator) Consequence(fixed []*Expr, consequence *Expr) bool {
	return p.ConsequenceWithEqs(fixed, nil, nil, consequence)
}

// ConsequenceWithEqs propagates a consequence based on fixed values and equalities.
// fixed are the premise fixed terms, lhs/rhs are equality premises, consequence is the result.
// Returns true if the propagation was accepted.
func (p *UserPropagator) ConsequenceWithEqs(fixed []*Expr, lhs []*Expr, rhs []*Expr, consequence *Expr) bool {
	numFixed := C.uint(len(fixed))
	numEqs := C.uint(len(lhs))
	var fixedPtr *C.Z3_ast
	var lhsPtr *C.Z3_ast
	var rhsPtr *C.Z3_ast
	if numFixed > 0 {
		cFixed := make([]C.Z3_ast, numFixed)
		for i, e := range fixed {
			cFixed[i] = e.ptr
		}
		fixedPtr = &cFixed[0]
	}
	if numEqs > 0 {
		cLhs := make([]C.Z3_ast, numEqs)
		cRhs := make([]C.Z3_ast, numEqs)
		for i := range lhs {
			cLhs[i] = lhs[i].ptr
			cRhs[i] = rhs[i].ptr
		}
		lhsPtr = &cLhs[0]
		rhsPtr = &cRhs[0]
	}
	result := C.Z3_solver_propagate_consequence(p.ctx.ptr, p.cb,
		numFixed, fixedPtr,
		numEqs, lhsPtr, rhsPtr,
		consequence.ptr)
	return result == C.bool(true)
}

// NextSplit overrides the solver's next variable to split on.
// This should be called during the Decide callback to override the decision.
// phase: -1 for false, 0 for default, 1 for true (as Z3_lbool values).
func (p *UserPropagator) NextSplit(e *Expr, idx uint, phase int) bool {
	result := C.Z3_solver_next_split(p.ctx.ptr, p.cb, e.ptr, C.uint(idx), C.Z3_lbool(phase))
	return result == C.bool(true)
}

// PropagatorDeclare creates an uninterpreted function declaration for the user propagator.
// When expressions using this function are created, the Created callback is invoked.
func (ctx *Context) PropagatorDeclare(name string, domain []*Sort, rangeSort *Sort) *FuncDecl {
	sym := ctx.MkStringSymbol(name)
	n := C.uint(len(domain))
	var domainPtr *C.Z3_sort
	if n > 0 {
		cDomain := make([]C.Z3_sort, n)
		for i, s := range domain {
			cDomain[i] = s.ptr
		}
		domainPtr = &cDomain[0]
	}
	result := C.Z3_solver_propagate_declare(ctx.ptr, sym.ptr, n, domainPtr, rangeSort.ptr)
	return newFuncDecl(ctx, result)
}

// NewUserPropagator attaches a user propagator to the solver.
// The callbacks object must implement UserPropagatorCallbacks (Push, Pop, Fresh).
// Optional callbacks (Fixed, Final, Eq, Diseq, Created, Decide, OnBinding)
// are registered by calling the corresponding Register* methods on the returned propagator.
//
// The propagator must be closed by calling Close() when no longer needed.
func (s *Solver) NewUserPropagator(callbacks UserPropagatorCallbacks) *UserPropagator {
	return newUserPropagator(s.ctx, s, callbacks)
}

// OnClauseHandler is the callback function type for clause inference events.
// proofHint is a partial derivation justifying the inference (may be nil).
// deps contains dependency indices.
// literals is the inferred clause as an AST vector.
// The lifetime of proofHint and literals is limited to the callback scope.
type OnClauseHandler func(proofHint *Expr, deps []uint, literals *ASTVector)

// OnClause registers a callback for clause inferences during solving.
// Useful for observing learned clauses, custom learning strategies,
// clause sharing in parallel solvers, and proof extraction.
// Call Close when the callback is no longer needed.
type OnClause struct {
	handle  cgo.Handle
	ctx     *Context
	handler OnClauseHandler
}

// NewOnClause registers a callback for clause inferences on the given solver.
// The returned OnClause must be closed by calling Close() when done.
func (s *Solver) NewOnClause(handler OnClauseHandler) *OnClause {
	oc := &OnClause{
		ctx:     s.ctx,
		handler: handler,
	}
	oc.handle = cgo.NewHandle(oc)
	C.z3go_solver_register_on_clause(s.ctx.ptr, s.ptr, C.uintptr_t(oc.handle))
	return oc
}

// Close releases the resources associated with this on-clause callback.
func (oc *OnClause) Close() {
	if oc.handle != 0 {
		oc.handle.Delete()
		oc.handle = 0
	}
}
