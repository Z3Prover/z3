package z3

/*
#include "z3.h"
#include <stdint.h>
*/
import "C"
import (
	"runtime/cgo"
	"unsafe"
)

// withCallback temporarily sets the callback context, calls fn, and restores the old context.
func (p *UserPropagator) withCallback(cb C.Z3_solver_callback, fn func()) {
	old := p.cb
	p.cb = cb
	defer func() { p.cb = old }()
	fn()
}

// goPushCb is exported to C as a callback for Z3_push_eh.
//
//export goPushCb
func goPushCb(ctx C.uintptr_t, cb C.Z3_solver_callback) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	p.withCallback(cb, p.iface.Push)
}

// goPopCb is exported to C as a callback for Z3_pop_eh.
//
//export goPopCb
func goPopCb(ctx C.uintptr_t, cb C.Z3_solver_callback, numScopes C.uint) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	p.withCallback(cb, func() {
		p.iface.Pop(uint(numScopes))
	})
}

// goFreshCb is exported to C as a callback for Z3_fresh_eh.
//
//export goFreshCb
func goFreshCb(ctx C.uintptr_t, newContext C.Z3_context) C.uintptr_t {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	freshCtx := &Context{ptr: newContext}
	freshIface := p.iface.Fresh(freshCtx)
	freshProp := &UserPropagator{
		ctx:   freshCtx,
		iface: freshIface,
	}
	freshProp.handle = cgo.NewHandle(freshProp)
	return C.uintptr_t(freshProp.handle)
}

// goFixedCb is exported to C as a callback for Z3_fixed_eh.
//
//export goFixedCb
func goFixedCb(ctx C.uintptr_t, cb C.Z3_solver_callback, t C.Z3_ast, value C.Z3_ast) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(FixedHandler); ok {
		p.withCallback(cb, func() {
			h.Fixed(newExpr(p.ctx, t), newExpr(p.ctx, value))
		})
	}
}

// goEqCb is exported to C as a callback for Z3_eq_eh (equality).
//
//export goEqCb
func goEqCb(ctx C.uintptr_t, cb C.Z3_solver_callback, s C.Z3_ast, t C.Z3_ast) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(EqHandler); ok {
		p.withCallback(cb, func() {
			h.Eq(newExpr(p.ctx, s), newExpr(p.ctx, t))
		})
	}
}

// goDiseqCb is exported to C as a callback for Z3_eq_eh (disequality).
//
//export goDiseqCb
func goDiseqCb(ctx C.uintptr_t, cb C.Z3_solver_callback, s C.Z3_ast, t C.Z3_ast) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(DiseqHandler); ok {
		p.withCallback(cb, func() {
			h.Diseq(newExpr(p.ctx, s), newExpr(p.ctx, t))
		})
	}
}

// goFinalCb is exported to C as a callback for Z3_final_eh.
//
//export goFinalCb
func goFinalCb(ctx C.uintptr_t, cb C.Z3_solver_callback) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(FinalHandler); ok {
		p.withCallback(cb, h.Final)
	}
}

// goCreatedCb is exported to C as a callback for Z3_created_eh.
//
//export goCreatedCb
func goCreatedCb(ctx C.uintptr_t, cb C.Z3_solver_callback, t C.Z3_ast) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(CreatedHandler); ok {
		p.withCallback(cb, func() {
			h.Created(newExpr(p.ctx, t))
		})
	}
}

// goDecideCb is exported to C as a callback for Z3_decide_eh.
//
//export goDecideCb
func goDecideCb(ctx C.uintptr_t, cb C.Z3_solver_callback, t C.Z3_ast, idx C.uint, phase C.bool) {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	if h, ok := p.iface.(DecideHandler); ok {
		p.withCallback(cb, func() {
			h.Decide(newExpr(p.ctx, t), uint(idx), phase == C.bool(true))
		})
	}
}

// goOnBindingCb is exported to C as a callback for Z3_on_binding_eh.
//
//export goOnBindingCb
func goOnBindingCb(ctx C.uintptr_t, cb C.Z3_solver_callback, q C.Z3_ast, inst C.Z3_ast) C.bool {
	p := cgo.Handle(ctx).Value().(*UserPropagator)
	result := C.bool(true) // default: allow binding when handler is not implemented
	if h, ok := p.iface.(OnBindingHandler); ok {
		p.withCallback(cb, func() {
			if !h.OnBinding(newExpr(p.ctx, q), newExpr(p.ctx, inst)) {
				result = C.bool(false)
			}
		})
	}
	return result
}

// goOnClauseCb is exported to C as a callback for Z3_on_clause_eh.
//
//export goOnClauseCb
func goOnClauseCb(ctx C.uintptr_t, proofHint C.Z3_ast, n C.uint, deps *C.uint, literals C.Z3_ast_vector) {
	oc := cgo.Handle(ctx).Value().(*OnClause)
	var ph *Expr
	if proofHint != nil {
		ph = newExpr(oc.ctx, proofHint)
	}
	goDepSlice := make([]uint, uint(n))
	if n > 0 {
		depSlice := (*[1 << 28]C.uint)(unsafe.Pointer(deps))[:n:n]
		for i := uint(0); i < uint(n); i++ {
			goDepSlice[i] = uint(depSlice[i])
		}
	}
	vec := newASTVector(oc.ctx, literals)
	oc.handler(ph, goDepSlice, vec)
}
