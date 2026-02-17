package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"runtime"
	"unsafe"
)

// Optimize represents a Z3 optimization context for solving optimization problems.
// Unlike Solver which only checks satisfiability, Optimize can find optimal solutions
// with respect to objective functions.
type Optimize struct {
	ctx *Context
	ptr C.Z3_optimize
}

// NewOptimize creates a new optimization context.
func (c *Context) NewOptimize() *Optimize {
	opt := &Optimize{
		ctx: c,
		ptr: C.Z3_mk_optimize(c.ptr),
	}
	C.Z3_optimize_inc_ref(c.ptr, opt.ptr)
	runtime.SetFinalizer(opt, func(o *Optimize) {
		C.Z3_optimize_dec_ref(o.ctx.ptr, o.ptr)
	})
	return opt
}

// String returns the string representation of the optimize context.
func (o *Optimize) String() string {
	return C.GoString(C.Z3_optimize_to_string(o.ctx.ptr, o.ptr))
}

// Assert adds a constraint to the optimizer.
func (o *Optimize) Assert(constraint *Expr) {
	C.Z3_optimize_assert(o.ctx.ptr, o.ptr, constraint.ptr)
}

// AssertAndTrack adds a constraint with a tracking literal for unsat core extraction.
func (o *Optimize) AssertAndTrack(constraint, track *Expr) {
	C.Z3_optimize_assert_and_track(o.ctx.ptr, o.ptr, constraint.ptr, track.ptr)
}

// AssertSoft adds a soft constraint with a weight.
// Soft constraints are used for MaxSMT problems.
// Returns a handle to the objective.
func (o *Optimize) AssertSoft(constraint *Expr, weight string, group string) uint {
	cWeight := C.CString(weight)
	cGroup := C.CString(group)
	defer C.free(unsafe.Pointer(cWeight))
	defer C.free(unsafe.Pointer(cGroup))

	sym := o.ctx.MkStringSymbol(group)
	return uint(C.Z3_optimize_assert_soft(o.ctx.ptr, o.ptr, constraint.ptr, cWeight, sym.ptr))
}

// Maximize adds a maximization objective.
// Returns a handle to the objective that can be used to retrieve bounds.
func (o *Optimize) Maximize(expr *Expr) uint {
	return uint(C.Z3_optimize_maximize(o.ctx.ptr, o.ptr, expr.ptr))
}

// Minimize adds a minimization objective.
// Returns a handle to the objective that can be used to retrieve bounds.
func (o *Optimize) Minimize(expr *Expr) uint {
	return uint(C.Z3_optimize_minimize(o.ctx.ptr, o.ptr, expr.ptr))
}

// Check checks the satisfiability of the constraints and optimizes objectives.
func (o *Optimize) Check(assumptions ...*Expr) Status {
	var result C.Z3_lbool
	if len(assumptions) == 0 {
		result = C.Z3_optimize_check(o.ctx.ptr, o.ptr, 0, nil)
	} else {
		cAssumptions := make([]C.Z3_ast, len(assumptions))
		for i, a := range assumptions {
			cAssumptions[i] = a.ptr
		}
		result = C.Z3_optimize_check(o.ctx.ptr, o.ptr, C.uint(len(assumptions)), &cAssumptions[0])
	}
	return Status(result)
}

// Model returns the model if the constraints are satisfiable.
func (o *Optimize) Model() *Model {
	modelPtr := C.Z3_optimize_get_model(o.ctx.ptr, o.ptr)
	if modelPtr == nil {
		return nil
	}
	return newModel(o.ctx, modelPtr)
}

// Push creates a backtracking point.
func (o *Optimize) Push() {
	C.Z3_optimize_push(o.ctx.ptr, o.ptr)
}

// Pop removes a backtracking point.
func (o *Optimize) Pop() {
	C.Z3_optimize_pop(o.ctx.ptr, o.ptr)
}

// GetLower retrieves a lower bound for the objective at the given index.
func (o *Optimize) GetLower(index uint) *Expr {
	result := C.Z3_optimize_get_lower(o.ctx.ptr, o.ptr, C.uint(index))
	if result == nil {
		return nil
	}
	return newExpr(o.ctx, result)
}

// GetUpper retrieves an upper bound for the objective at the given index.
func (o *Optimize) GetUpper(index uint) *Expr {
	result := C.Z3_optimize_get_upper(o.ctx.ptr, o.ptr, C.uint(index))
	if result == nil {
		return nil
	}
	return newExpr(o.ctx, result)
}

// GetLowerAsVector retrieves a lower bound as a vector (inf, value, eps).
// The objective value is unbounded if inf is non-zero,
// otherwise it's represented as value + eps * EPSILON.
func (o *Optimize) GetLowerAsVector(index uint) []*Expr {
	vec := C.Z3_optimize_get_lower_as_vector(o.ctx.ptr, o.ptr, C.uint(index))
	result := astVectorToExprs(o.ctx, vec)
	if len(result) != 3 {
		return nil
	}
	return result
}

// GetUpperAsVector retrieves an upper bound as a vector (inf, value, eps).
// The objective value is unbounded if inf is non-zero,
// otherwise it's represented as value + eps * EPSILON.
func (o *Optimize) GetUpperAsVector(index uint) []*Expr {
	vec := C.Z3_optimize_get_upper_as_vector(o.ctx.ptr, o.ptr, C.uint(index))
	result := astVectorToExprs(o.ctx, vec)
	if len(result) != 3 {
		return nil
	}
	return result
}

// ReasonUnknown returns the reason why the result is unknown.
func (o *Optimize) ReasonUnknown() string {
	return C.GoString(C.Z3_optimize_get_reason_unknown(o.ctx.ptr, o.ptr))
}

// GetHelp returns help information for the optimizer.
func (o *Optimize) GetHelp() string {
	return C.GoString(C.Z3_optimize_get_help(o.ctx.ptr, o.ptr))
}

// SetParams sets parameters for the optimizer.
func (o *Optimize) SetParams(params *Params) {
	C.Z3_optimize_set_params(o.ctx.ptr, o.ptr, params.ptr)
}

// Assertions returns the assertions in the optimizer.
func (o *Optimize) Assertions() []*Expr {
	vec := C.Z3_optimize_get_assertions(o.ctx.ptr, o.ptr)
	return astVectorToExprs(o.ctx, vec)
}

// Objectives returns the objectives in the optimizer.
func (o *Optimize) Objectives() []*Expr {
	vec := C.Z3_optimize_get_objectives(o.ctx.ptr, o.ptr)
	return astVectorToExprs(o.ctx, vec)
}

// UnsatCore returns the unsat core if the constraints are unsatisfiable.
func (o *Optimize) UnsatCore() []*Expr {
	vec := C.Z3_optimize_get_unsat_core(o.ctx.ptr, o.ptr)
	return astVectorToExprs(o.ctx, vec)
}

// FromFile parses an SMT-LIB2 file with optimization objectives and constraints.
func (o *Optimize) FromFile(filename string) {
	cFilename := C.CString(filename)
	defer C.free(unsafe.Pointer(cFilename))
	C.Z3_optimize_from_file(o.ctx.ptr, o.ptr, cFilename)
}

// FromString parses an SMT-LIB2 string with optimization objectives and constraints.
func (o *Optimize) FromString(s string) {
	cStr := C.CString(s)
	defer C.free(unsafe.Pointer(cStr))
	C.Z3_optimize_from_string(o.ctx.ptr, o.ptr, cStr)
}
