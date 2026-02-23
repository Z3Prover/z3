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
	return astVectorToExprs(s.ctx, vec)
}

// UnsatCore returns the unsat core if the constraints are unsatisfiable.
func (s *Solver) UnsatCore() []*Expr {
	vec := C.Z3_solver_get_unsat_core(s.ctx.ptr, s.ptr)
	return astVectorToExprs(s.ctx, vec)
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

// Units returns the unit clauses (literals) learned by the solver.
// Unit clauses are assertions that have been simplified to single literals.
// This is useful for debugging and understanding solver behavior.
func (s *Solver) Units() []*Expr {
	vec := C.Z3_solver_get_units(s.ctx.ptr, s.ptr)
	return astVectorToExprs(s.ctx, vec)
}

// NonUnits returns the non-unit clauses in the solver's current state.
// These are clauses that have not been reduced to unit clauses.
// This is useful for debugging and understanding solver behavior.
func (s *Solver) NonUnits() []*Expr {
	vec := C.Z3_solver_get_non_units(s.ctx.ptr, s.ptr)
	return astVectorToExprs(s.ctx, vec)
}

// Trail returns the decision trail of the solver.
// The trail contains the sequence of literals assigned during search.
// This is useful for understanding the solver's decision history.
// Note: This function works primarily with SimpleSolver. For solvers created
// using tactics (e.g., NewSolver()), it may return an error.
func (s *Solver) Trail() []*Expr {
	vec := C.Z3_solver_get_trail(s.ctx.ptr, s.ptr)
	return astVectorToExprs(s.ctx, vec)
}

// TrailLevels returns the decision levels for each literal in the trail.
// The returned slice has the same length as the trail, where each element
// indicates the decision level at which the corresponding trail literal was assigned.
// This is useful for understanding the structure of the search tree.
// Note: This function works primarily with SimpleSolver. For solvers created
// using tactics (e.g., NewSolver()), it may return an error.
func (s *Solver) TrailLevels() []uint {
	// Get the trail vector directly from the C API
	trailVec := C.Z3_solver_get_trail(s.ctx.ptr, s.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, trailVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, trailVec)

	n := uint(C.Z3_ast_vector_size(s.ctx.ptr, trailVec))
	if n == 0 {
		return []uint{}
	}

	// Allocate the levels array
	levels := make([]C.uint, n)

	// Get the levels using the trail vector directly
	// Safe to pass &levels[0] because we checked n > 0 above
	C.Z3_solver_get_levels(s.ctx.ptr, s.ptr, trailVec, C.uint(n), &levels[0])

	// Convert to Go slice
	result := make([]uint, n)
	for i := uint(0); i < n; i++ {
		result[i] = uint(levels[i])
	}
	return result
}

// CongruenceRoot returns the congruence class representative of the given expression.
// This returns the root element in the congruence closure for the term.
// Note: This function works primarily with SimpleSolver. Terms and variables that
// are eliminated during pre-processing are not visible to the congruence closure.
func (s *Solver) CongruenceRoot(expr *Expr) *Expr {
	ast := C.Z3_solver_congruence_root(s.ctx.ptr, s.ptr, expr.ptr)
	return newExpr(s.ctx, ast)
}

// CongruenceNext returns the next element in the congruence class of the given expression.
// This allows iteration through all elements in a congruence class.
// Note: This function works primarily with SimpleSolver. Terms and variables that
// are eliminated during pre-processing are not visible to the congruence closure.
func (s *Solver) CongruenceNext(expr *Expr) *Expr {
	ast := C.Z3_solver_congruence_next(s.ctx.ptr, s.ptr, expr.ptr)
	return newExpr(s.ctx, ast)
}

// CongruenceExplain returns an explanation for why two expressions are congruent.
// The result is an expression that justifies the congruence between a and b.
// Note: This function works primarily with SimpleSolver. Terms and variables that
// are eliminated during pre-processing are not visible to the congruence closure.
func (s *Solver) CongruenceExplain(a, b *Expr) *Expr {
	ast := C.Z3_solver_congruence_explain(s.ctx.ptr, s.ptr, a.ptr, b.ptr)
	return newExpr(s.ctx, ast)
}

// SetInitialValue provides an initial value hint for a variable to the solver.
// This can help guide the solver to find solutions more efficiently.
// The variable must be a constant or function application, and the value must be
// compatible with the variable's sort.
func (s *Solver) SetInitialValue(variable, value *Expr) {
	C.Z3_solver_set_initial_value(s.ctx.ptr, s.ptr, variable.ptr, value.ptr)
}

// Cube extracts a cube (conjunction of literals) from the solver state.
// vars is an optional list of variables to use as cube variables; if nil, the solver decides.
// cutoff specifies the backtrack level cutoff for cube generation.
// Returns a slice of expressions representing the cube, or nil when the search space is exhausted.
func (s *Solver) Cube(vars []*Expr, cutoff uint) []*Expr {
	varVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, varVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, varVec)
	for _, v := range vars {
		C.Z3_ast_vector_push(s.ctx.ptr, varVec, v.ptr)
	}
	result := C.Z3_solver_cube(s.ctx.ptr, s.ptr, varVec, C.uint(cutoff))
	return astVectorToExprs(s.ctx, result)
}

// GetConsequences retrieves fixed assignments for variables given assumptions.
// Returns the status and the set of consequences as implications.
func (s *Solver) GetConsequences(assumptions []*Expr, variables []*Expr) (Status, []*Expr) {
	asmVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, asmVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, asmVec)
	varVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, varVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, varVec)
	consVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, consVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, consVec)
	for _, a := range assumptions {
		C.Z3_ast_vector_push(s.ctx.ptr, asmVec, a.ptr)
	}
	for _, v := range variables {
		C.Z3_ast_vector_push(s.ctx.ptr, varVec, v.ptr)
	}
	r := Status(C.Z3_solver_get_consequences(s.ctx.ptr, s.ptr, asmVec, varVec, consVec))
	return r, astVectorToExprs(s.ctx, consVec)
}

// SolveFor solves constraints treating given variables symbolically.
// variables are the variables to solve for, terms are the substitution terms,
// and guards are the Boolean guards for the substitutions.
func (s *Solver) SolveFor(variables []*Expr, terms []*Expr, guards []*Expr) {
	varVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, varVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, varVec)
	termVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, termVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, termVec)
	guardVec := C.Z3_mk_ast_vector(s.ctx.ptr)
	C.Z3_ast_vector_inc_ref(s.ctx.ptr, guardVec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.ptr, guardVec)
	for _, v := range variables {
		C.Z3_ast_vector_push(s.ctx.ptr, varVec, v.ptr)
	}
	for _, t := range terms {
		C.Z3_ast_vector_push(s.ctx.ptr, termVec, t.ptr)
	}
	for _, g := range guards {
		C.Z3_ast_vector_push(s.ctx.ptr, guardVec, g.ptr)
	}
	C.Z3_solver_solve_for(s.ctx.ptr, s.ptr, varVec, termVec, guardVec)
}

// ImportModelConverter imports the model converter from src into this solver.
// This transfers model simplifications from one solver instance to another,
// useful when combining results from multiple solver instances.
func (dst *Solver) ImportModelConverter(src *Solver) {
	C.Z3_solver_import_model_converter(dst.ctx.ptr, src.ptr, dst.ptr)
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

// SortUniverse returns the universe of values for an uninterpreted sort in the model.
// The universe is represented as a list of distinct expressions.
// Returns nil if the sort is not an uninterpreted sort in this model.
func (m *Model) SortUniverse(sort *Sort) []*Expr {
	vec := C.Z3_model_get_sort_universe(m.ctx.ptr, m.ptr, sort.ptr)
	if vec == nil {
		return nil
	}
	return astVectorToExprs(m.ctx, vec)
}
