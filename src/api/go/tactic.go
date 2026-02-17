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

// Tactic represents a Z3 tactic for transforming goals.
type Tactic struct {
	ctx *Context
	ptr C.Z3_tactic
}

// newTactic creates a new Tactic and manages its reference count.
func newTactic(ctx *Context, ptr C.Z3_tactic) *Tactic {
	t := &Tactic{ctx: ctx, ptr: ptr}
	C.Z3_tactic_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(t, func(tactic *Tactic) {
		C.Z3_tactic_dec_ref(tactic.ctx.ptr, tactic.ptr)
	})
	return t
}

// MkTactic creates a tactic with the given name.
func (c *Context) MkTactic(name string) *Tactic {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))
	return newTactic(c, C.Z3_mk_tactic(c.ptr, cName))
}

// Apply applies the tactic to a goal.
func (t *Tactic) Apply(g *Goal) *ApplyResult {
	return newApplyResult(t.ctx, C.Z3_tactic_apply(t.ctx.ptr, t.ptr, g.ptr))
}

// GetHelp returns help information for the tactic.
func (t *Tactic) GetHelp() string {
	return C.GoString(C.Z3_tactic_get_help(t.ctx.ptr, t.ptr))
}

// AndThen creates a tactic that applies t1 and then t2.
func (t *Tactic) AndThen(t2 *Tactic) *Tactic {
	return newTactic(t.ctx, C.Z3_tactic_and_then(t.ctx.ptr, t.ptr, t2.ptr))
}

// OrElse creates a tactic that applies t1, and if it fails, applies t2.
func (t *Tactic) OrElse(t2 *Tactic) *Tactic {
	return newTactic(t.ctx, C.Z3_tactic_or_else(t.ctx.ptr, t.ptr, t2.ptr))
}

// Repeat creates a tactic that applies t repeatedly (at most max times).
func (t *Tactic) Repeat(max uint) *Tactic {
	return newTactic(t.ctx, C.Z3_tactic_repeat(t.ctx.ptr, t.ptr, C.uint(max)))
}

// When creates a conditional tactic that applies t only if probe p evaluates to true.
func (c *Context) TacticWhen(p *Probe, t *Tactic) *Tactic {
	return newTactic(c, C.Z3_tactic_when(c.ptr, p.ptr, t.ptr))
}

// TacticCond creates a conditional tactic: if p then t1 else t2.
func (c *Context) TacticCond(p *Probe, t1, t2 *Tactic) *Tactic {
	return newTactic(c, C.Z3_tactic_cond(c.ptr, p.ptr, t1.ptr, t2.ptr))
}

// TacticFail creates a tactic that always fails.
func (c *Context) TacticFail() *Tactic {
	return newTactic(c, C.Z3_tactic_fail(c.ptr))
}

// TacticSkip creates a tactic that always succeeds.
func (c *Context) TacticSkip() *Tactic {
	return newTactic(c, C.Z3_tactic_skip(c.ptr))
}

// Goal represents a set of formulas that can be solved or transformed.
type Goal struct {
	ctx *Context
	ptr C.Z3_goal
}

// newGoal creates a new Goal and manages its reference count.
func newGoal(ctx *Context, ptr C.Z3_goal) *Goal {
	g := &Goal{ctx: ctx, ptr: ptr}
	C.Z3_goal_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(g, func(goal *Goal) {
		C.Z3_goal_dec_ref(goal.ctx.ptr, goal.ptr)
	})
	return g
}

// MkGoal creates a new goal.
func (c *Context) MkGoal(models, unsatCores, proofs bool) *Goal {
	return newGoal(c, C.Z3_mk_goal(c.ptr, C.bool(models), C.bool(unsatCores), C.bool(proofs)))
}

// Assert adds a constraint to the goal.
func (g *Goal) Assert(constraint *Expr) {
	C.Z3_goal_assert(g.ctx.ptr, g.ptr, constraint.ptr)
}

// Size returns the number of formulas in the goal.
func (g *Goal) Size() uint {
	return uint(C.Z3_goal_size(g.ctx.ptr, g.ptr))
}

// Formula returns the i-th formula in the goal.
func (g *Goal) Formula(i uint) *Expr {
	return newExpr(g.ctx, C.Z3_goal_formula(g.ctx.ptr, g.ptr, C.uint(i)))
}

// NumExprs returns the number of expressions in the goal.
func (g *Goal) NumExprs() uint {
	return uint(C.Z3_goal_num_exprs(g.ctx.ptr, g.ptr))
}

// IsDecidedSat returns true if the goal is decided to be satisfiable.
func (g *Goal) IsDecidedSat() bool {
	return bool(C.Z3_goal_is_decided_sat(g.ctx.ptr, g.ptr))
}

// IsDecidedUnsat returns true if the goal is decided to be unsatisfiable.
func (g *Goal) IsDecidedUnsat() bool {
	return bool(C.Z3_goal_is_decided_unsat(g.ctx.ptr, g.ptr))
}

// Reset removes all formulas from the goal.
func (g *Goal) Reset() {
	C.Z3_goal_reset(g.ctx.ptr, g.ptr)
}

// String returns the string representation of the goal.
func (g *Goal) String() string {
	return C.GoString(C.Z3_goal_to_string(g.ctx.ptr, g.ptr))
}

// ApplyResult represents the result of applying a tactic to a goal.
type ApplyResult struct {
	ctx *Context
	ptr C.Z3_apply_result
}

// newApplyResult creates a new ApplyResult and manages its reference count.
func newApplyResult(ctx *Context, ptr C.Z3_apply_result) *ApplyResult {
	ar := &ApplyResult{ctx: ctx, ptr: ptr}
	C.Z3_apply_result_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(ar, func(result *ApplyResult) {
		C.Z3_apply_result_dec_ref(result.ctx.ptr, result.ptr)
	})
	return ar
}

// NumSubgoals returns the number of subgoals in the result.
func (ar *ApplyResult) NumSubgoals() uint {
	return uint(C.Z3_apply_result_get_num_subgoals(ar.ctx.ptr, ar.ptr))
}

// Subgoal returns the i-th subgoal.
func (ar *ApplyResult) Subgoal(i uint) *Goal {
	return newGoal(ar.ctx, C.Z3_apply_result_get_subgoal(ar.ctx.ptr, ar.ptr, C.uint(i)))
}

// String returns the string representation of the apply result.
func (ar *ApplyResult) String() string {
	return C.GoString(C.Z3_apply_result_to_string(ar.ctx.ptr, ar.ptr))
}

// Probe represents a probe for checking properties of goals.
type Probe struct {
	ctx *Context
	ptr C.Z3_probe
}

// newProbe creates a new Probe and manages its reference count.
func newProbe(ctx *Context, ptr C.Z3_probe) *Probe {
	p := &Probe{ctx: ctx, ptr: ptr}
	C.Z3_probe_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(p, func(probe *Probe) {
		C.Z3_probe_dec_ref(probe.ctx.ptr, probe.ptr)
	})
	return p
}

// MkProbe creates a probe with the given name.
func (c *Context) MkProbe(name string) *Probe {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))
	return newProbe(c, C.Z3_mk_probe(c.ptr, cName))
}

// Apply evaluates the probe on a goal.
func (p *Probe) Apply(g *Goal) float64 {
	return float64(C.Z3_probe_apply(p.ctx.ptr, p.ptr, g.ptr))
}

// ProbeConst creates a probe that always evaluates to the given value.
func (c *Context) ProbeConst(val float64) *Probe {
	return newProbe(c, C.Z3_probe_const(c.ptr, C.double(val)))
}

// ProbeLt creates a probe that evaluates to true if p1 < p2.
func (p *Probe) Lt(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_lt(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeGt creates a probe that evaluates to true if p1 > p2.
func (p *Probe) Gt(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_gt(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeLe creates a probe that evaluates to true if p1 <= p2.
func (p *Probe) Le(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_le(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeGe creates a probe that evaluates to true if p1 >= p2.
func (p *Probe) Ge(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_ge(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeEq creates a probe that evaluates to true if p1 == p2.
func (p *Probe) Eq(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_eq(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeAnd creates a probe that is the conjunction of p1 and p2.
func (p *Probe) And(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_and(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeOr creates a probe that is the disjunction of p1 and p2.
func (p *Probe) Or(p2 *Probe) *Probe {
	return newProbe(p.ctx, C.Z3_probe_or(p.ctx.ptr, p.ptr, p2.ptr))
}

// ProbeNot creates a probe that is the negation of p.
func (p *Probe) Not() *Probe {
	return newProbe(p.ctx, C.Z3_probe_not(p.ctx.ptr, p.ptr))
}

// Params represents a parameter set.
type Params struct {
	ctx *Context
	ptr C.Z3_params
}

// newParams creates a new Params and manages its reference count.
func newParams(ctx *Context, ptr C.Z3_params) *Params {
	params := &Params{ctx: ctx, ptr: ptr}
	C.Z3_params_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(params, func(p *Params) {
		C.Z3_params_dec_ref(p.ctx.ptr, p.ptr)
	})
	return params
}

// MkParams creates a new parameter set.
func (c *Context) MkParams() *Params {
	return newParams(c, C.Z3_mk_params(c.ptr))
}

// SetBool sets a Boolean parameter.
func (p *Params) SetBool(key string, value bool) {
	sym := p.ctx.MkStringSymbol(key)
	C.Z3_params_set_bool(p.ctx.ptr, p.ptr, sym.ptr, C.bool(value))
}

// SetUint sets an unsigned integer parameter.
func (p *Params) SetUint(key string, value uint) {
	sym := p.ctx.MkStringSymbol(key)
	C.Z3_params_set_uint(p.ctx.ptr, p.ptr, sym.ptr, C.uint(value))
}

// SetDouble sets a double parameter.
func (p *Params) SetDouble(key string, value float64) {
	sym := p.ctx.MkStringSymbol(key)
	C.Z3_params_set_double(p.ctx.ptr, p.ptr, sym.ptr, C.double(value))
}

// SetSymbol sets a symbol parameter.
func (p *Params) SetSymbol(key string, value *Symbol) {
	sym := p.ctx.MkStringSymbol(key)
	C.Z3_params_set_symbol(p.ctx.ptr, p.ptr, sym.ptr, value.ptr)
}

// String returns the string representation of the parameters.
func (p *Params) String() string {
	return C.GoString(C.Z3_params_to_string(p.ctx.ptr, p.ptr))
}
