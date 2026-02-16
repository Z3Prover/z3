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

// Status represents the result of a satisfiability check.
type Status int

const (
	// Unsatisfiable means the constraints are unsatisfiable.
	Unsatisfiable Status = -1
	// Unknown means Z3 could not determine satisfiability.
	Unknown Status = 0
	// Satisfiable means the constraints are satisfiable.
	Satisfiable Status = 1
)

// String returns the string representation of the status.
func (s Status) String() string {
	switch s {
	case Unsatisfiable:
		return "unsat"
	case Unknown:
		return "unknown"
	case Satisfiable:
		return "sat"
	default:
		return "unknown"
	}
}

// Solver represents a Z3 solver.
type Solver struct {
	ctx *Context
	ptr C.Z3_solver
}

// NewSolver creates a new solver for the given context.
func (c *Context) NewSolver() *Solver {
	s := &Solver{
		ctx: c,
		ptr: C.Z3_mk_solver(c.ptr),
	}
	C.Z3_solver_inc_ref(c.ptr, s.ptr)
	runtime.SetFinalizer(s, func(solver *Solver) {
		C.Z3_solver_dec_ref(solver.ctx.ptr, solver.ptr)
	})
	return s
}

// NewSolverForLogic creates a solver for a specific logic.
func (c *Context) NewSolverForLogic(logic string) *Solver {
	sym := c.MkStringSymbol(logic)
	s := &Solver{
		ctx: c,
		ptr: C.Z3_mk_solver_for_logic(c.ptr, sym.ptr),
	}
	C.Z3_solver_inc_ref(c.ptr, s.ptr)
	runtime.SetFinalizer(s, func(solver *Solver) {
		C.Z3_solver_dec_ref(solver.ctx.ptr, solver.ptr)
	})
	return s
}

// String returns the string representation of the solver.
func (s *Solver) String() string {
	return C.GoString(C.Z3_solver_to_string(s.ctx.ptr, s.ptr))
}

// Assert adds a constraint to the solver.
func (s *Solver) Assert(constraint *Expr) {
	C.Z3_solver_assert(s.ctx.ptr, s.ptr, constraint.ptr)
}

// AssertAndTrack adds a constraint with a tracking literal.
func (s *Solver) AssertAndTrack(constraint, track *Expr) {
	C.Z3_solver_assert_and_track(s.ctx.ptr, s.ptr, constraint.ptr, track.ptr)
}

// Check checks the satisfiability of the constraints.
func (s *Solver) Check() Status {
	result := C.Z3_solver_check(s.ctx.ptr, s.ptr)
	return Status(result)
}

// CheckAssumptions checks satisfiability under assumptions.
func (s *Solver) CheckAssumptions(assumptions ...*Expr) Status {
	if len(assumptions) == 0 {
		return s.Check()
	}
	cAssumptions := make([]C.Z3_ast, len(assumptions))
	for i, a := range assumptions {
		cAssumptions[i] = a.ptr
	}
	result := C.Z3_solver_check_assumptions(s.ctx.ptr, s.ptr, C.uint(len(assumptions)), &cAssumptions[0])
	return Status(result)
}

// Model returns the model if the constraints are satisfiable.
func (s *Solver) Model() *Model {
	modelPtr := C.Z3_solver_get_model(s.ctx.ptr, s.ptr)
	if modelPtr == nil {
		return nil
	}
	return newModel(s.ctx, modelPtr)
}

// Push creates a backtracking point.
func (s *Solver) Push() {
	C.Z3_solver_push(s.ctx.ptr, s.ptr)
}

// Pop removes backtracking points.
func (s *Solver) Pop(n uint) {
	C.Z3_solver_pop(s.ctx.ptr, s.ptr, C.uint(n))
}

// Reset removes all assertions from the solver.
func (s *Solver) Reset() {
	C.Z3_solver_reset(s.ctx.ptr, s.ptr)
}

// NumScopes returns the number of backtracking points.
func (s *Solver) NumScopes() uint {
	return uint(C.Z3_solver_get_num_scopes(s.ctx.ptr, s.ptr))
}

// Assertions returns the assertions in the solver.
func (s *Solver) Assertions() []*Expr {
	vec := C.Z3_solver_get_assertions(s.ctx.ptr, s.ptr)
	size := uint(C.Z3_ast_vector_size(s.ctx.ptr, vec))
	result := make([]*Expr, size)
	for i := uint(0); i < size; i++ {
		result[i] = newExpr(s.ctx, C.Z3_ast_vector_get(s.ctx.ptr, vec, C.uint(i)))
	}
	return result
}

// UnsatCore returns the unsat core if the constraints are unsatisfiable.
func (s *Solver) UnsatCore() []*Expr {
	vec := C.Z3_solver_get_unsat_core(s.ctx.ptr, s.ptr)
	size := uint(C.Z3_ast_vector_size(s.ctx.ptr, vec))
	result := make([]*Expr, size)
	for i := uint(0); i < size; i++ {
		result[i] = newExpr(s.ctx, C.Z3_ast_vector_get(s.ctx.ptr, vec, C.uint(i)))
	}
	return result
}

// ReasonUnknown returns the reason why the result is unknown.
func (s *Solver) ReasonUnknown() string {
	return C.GoString(C.Z3_solver_get_reason_unknown(s.ctx.ptr, s.ptr))
}

// GetStatistics returns the statistics for the solver.
// Statistics include performance metrics, memory usage, and decision statistics.
func (s *Solver) GetStatistics() *Statistics {
	ptr := C.Z3_solver_get_statistics(s.ctx.ptr, s.ptr)
	return newStatistics(s.ctx, ptr)
}

// FromFile parses and asserts SMT-LIB2 formulas from a file.
// The solver will contain the assertions from the file after this call.
func (s *Solver) FromFile(filename string) {
	cFilename := C.CString(filename)
	defer C.free(unsafe.Pointer(cFilename))
	C.Z3_solver_from_file(s.ctx.ptr, s.ptr, cFilename)
}

// FromString parses and asserts SMT-LIB2 formulas from a string.
// The solver will contain the assertions from the string after this call.
func (s *Solver) FromString(str string) {
	cStr := C.CString(str)
	defer C.free(unsafe.Pointer(cStr))
	C.Z3_solver_from_string(s.ctx.ptr, s.ptr, cStr)
}

// GetHelp returns a string describing all available solver parameters.
func (s *Solver) GetHelp() string {
	return C.GoString(C.Z3_solver_get_help(s.ctx.ptr, s.ptr))
}

// SetParams sets solver parameters.
// Parameters control solver behavior such as timeout, proof generation, etc.
func (s *Solver) SetParams(params *Params) {
	C.Z3_solver_set_params(s.ctx.ptr, s.ptr, params.ptr)
}

// GetParamDescrs returns parameter descriptions for the solver.
func (s *Solver) GetParamDescrs() *ParamDescrs {
	ptr := C.Z3_solver_get_param_descrs(s.ctx.ptr, s.ptr)
	return newParamDescrs(s.ctx, ptr)
}

// Interrupt interrupts the solver execution.
// This is useful for stopping long-running solver operations gracefully.
func (s *Solver) Interrupt() {
	C.Z3_solver_interrupt(s.ctx.ptr, s.ptr)
}

// Model represents a Z3 model (satisfying assignment).
type Model struct {
	ctx *Context
	ptr C.Z3_model
}

// newModel creates a new Model and manages its reference count.
func newModel(ctx *Context, ptr C.Z3_model) *Model {
	m := &Model{ctx: ctx, ptr: ptr}
	C.Z3_model_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(m, func(model *Model) {
		C.Z3_model_dec_ref(model.ctx.ptr, model.ptr)
	})
	return m
}

// String returns the string representation of the model.
func (m *Model) String() string {
	return C.GoString(C.Z3_model_to_string(m.ctx.ptr, m.ptr))
}

// NumConsts returns the number of constants in the model.
func (m *Model) NumConsts() uint {
	return uint(C.Z3_model_get_num_consts(m.ctx.ptr, m.ptr))
}

// NumFuncs returns the number of function interpretations in the model.
func (m *Model) NumFuncs() uint {
	return uint(C.Z3_model_get_num_funcs(m.ctx.ptr, m.ptr))
}

// GetConstDecl returns the i-th constant declaration in the model.
func (m *Model) GetConstDecl(i uint) *FuncDecl {
	return newFuncDecl(m.ctx, C.Z3_model_get_const_decl(m.ctx.ptr, m.ptr, C.uint(i)))
}

// GetFuncDecl returns the i-th function declaration in the model.
func (m *Model) GetFuncDecl(i uint) *FuncDecl {
	return newFuncDecl(m.ctx, C.Z3_model_get_func_decl(m.ctx.ptr, m.ptr, C.uint(i)))
}

// Eval evaluates an expression in the model.
// If modelCompletion is true, Z3 will assign an interpretation for uninterpreted constants.
func (m *Model) Eval(expr *Expr, modelCompletion bool) (*Expr, bool) {
	var result C.Z3_ast
	var completion C.bool
	if modelCompletion {
		completion = C.bool(true)
	} else {
		completion = C.bool(false)
	}
	success := C.Z3_model_eval(m.ctx.ptr, m.ptr, expr.ptr, completion, &result)
	if success == C.bool(false) {
		return nil, false
	}
	return newExpr(m.ctx, result), true
}

// GetConstInterp returns the interpretation of a constant.
func (m *Model) GetConstInterp(decl *FuncDecl) *Expr {
	result := C.Z3_model_get_const_interp(m.ctx.ptr, m.ptr, decl.ptr)
	if result == nil {
		return nil
	}
	return newExpr(m.ctx, result)
}

// FuncInterp represents a function interpretation in a model.
type FuncInterp struct {
	ctx *Context
	ptr C.Z3_func_interp
}

// GetFuncInterp returns the interpretation of a function.
func (m *Model) GetFuncInterp(decl *FuncDecl) *FuncInterp {
	result := C.Z3_model_get_func_interp(m.ctx.ptr, m.ptr, decl.ptr)
	if result == nil {
		return nil
	}
	fi := &FuncInterp{ctx: m.ctx, ptr: result}
	C.Z3_func_interp_inc_ref(m.ctx.ptr, result)
	runtime.SetFinalizer(fi, func(f *FuncInterp) {
		C.Z3_func_interp_dec_ref(f.ctx.ptr, f.ptr)
	})
	return fi
}

// NumEntries returns the number of entries in the function interpretation.
func (fi *FuncInterp) NumEntries() uint {
	return uint(C.Z3_func_interp_get_num_entries(fi.ctx.ptr, fi.ptr))
}

// GetElse returns the else value of the function interpretation.
func (fi *FuncInterp) GetElse() *Expr {
	result := C.Z3_func_interp_get_else(fi.ctx.ptr, fi.ptr)
	return newExpr(fi.ctx, result)
}

// GetArity returns the arity of the function interpretation.
func (fi *FuncInterp) GetArity() uint {
	return uint(C.Z3_func_interp_get_arity(fi.ctx.ptr, fi.ptr))
}
