// Copyright (c) Microsoft Corporation 2025
// Z3 Go API: Fixedpoint solver for Datalog and CHC (Constrained Horn Clauses)

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

// Fixedpoint represents a fixedpoint solver for Datalog/CHC queries
type Fixedpoint struct {
	ctx *Context
	ptr C.Z3_fixedpoint
}

// newFixedpoint creates a new Fixedpoint solver with proper memory management
func newFixedpoint(ctx *Context, ptr C.Z3_fixedpoint) *Fixedpoint {
	fp := &Fixedpoint{ctx: ctx, ptr: ptr}
	C.Z3_fixedpoint_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(fp, func(f *Fixedpoint) {
		C.Z3_fixedpoint_dec_ref(f.ctx.ptr, f.ptr)
	})
	return fp
}

// NewFixedpoint creates a new fixedpoint solver
func (ctx *Context) NewFixedpoint() *Fixedpoint {
	ptr := C.Z3_mk_fixedpoint(ctx.ptr)
	return newFixedpoint(ctx, ptr)
}

// GetHelp returns a string describing all available fixedpoint solver parameters
func (f *Fixedpoint) GetHelp() string {
	cstr := C.Z3_fixedpoint_get_help(f.ctx.ptr, f.ptr)
	return C.GoString(cstr)
}

// SetParams sets the fixedpoint solver parameters
func (f *Fixedpoint) SetParams(params *Params) {
	C.Z3_fixedpoint_set_params(f.ctx.ptr, f.ptr, params.ptr)
}

// GetParamDescrs retrieves parameter descriptions for the fixedpoint solver
func (f *Fixedpoint) GetParamDescrs() *ParamDescrs {
	ptr := C.Z3_fixedpoint_get_param_descrs(f.ctx.ptr, f.ptr)
	return newParamDescrs(f.ctx, ptr)
}

// Assert adds a constraint into the fixedpoint solver
func (f *Fixedpoint) Assert(constraint *Expr) {
	C.Z3_fixedpoint_assert(f.ctx.ptr, f.ptr, constraint.ptr)
}

// RegisterRelation registers a predicate as a recursive relation
func (f *Fixedpoint) RegisterRelation(funcDecl *FuncDecl) {
	C.Z3_fixedpoint_register_relation(f.ctx.ptr, f.ptr, funcDecl.ptr)
}

// AddRule adds a rule (Horn clause) to the fixedpoint solver
// The rule should be an implication of the form body => head
// where head is a relation and body is a conjunction of relations
func (f *Fixedpoint) AddRule(rule *Expr, name *Symbol) {
	var namePtr C.Z3_symbol
	if name != nil {
		namePtr = name.ptr
	} else {
		namePtr = nil
	}
	C.Z3_fixedpoint_add_rule(f.ctx.ptr, f.ptr, rule.ptr, namePtr)
}

// AddFact adds a table fact to the fixedpoint solver
func (f *Fixedpoint) AddFact(pred *FuncDecl, args []int) {
	if len(args) == 0 {
		C.Z3_fixedpoint_add_fact(f.ctx.ptr, f.ptr, pred.ptr, 0, nil)
		return
	}

	cArgs := make([]C.uint, len(args))
	for i, arg := range args {
		cArgs[i] = C.uint(arg)
	}
	C.Z3_fixedpoint_add_fact(f.ctx.ptr, f.ptr, pred.ptr, C.uint(len(args)), &cArgs[0])
}

// Query queries the fixedpoint solver with a constraint
// Returns Satisfiable if there is a derivation, Unsatisfiable if not
func (f *Fixedpoint) Query(query *Expr) Status {
	result := C.Z3_fixedpoint_query(f.ctx.ptr, f.ptr, query.ptr)
	switch result {
	case C.Z3_L_TRUE:
		return Satisfiable
	case C.Z3_L_FALSE:
		return Unsatisfiable
	default:
		return Unknown
	}
}

// QueryRelations queries the fixedpoint solver with an array of relations
// Returns Satisfiable if any relation is non-empty, Unsatisfiable otherwise
func (f *Fixedpoint) QueryRelations(relations []*FuncDecl) Status {
	if len(relations) == 0 {
		return Unknown
	}

	cRelations := make([]C.Z3_func_decl, len(relations))
	for i, rel := range relations {
		cRelations[i] = rel.ptr
	}

	result := C.Z3_fixedpoint_query_relations(f.ctx.ptr, f.ptr, C.uint(len(relations)), &cRelations[0])
	switch result {
	case C.Z3_L_TRUE:
		return Satisfiable
	case C.Z3_L_FALSE:
		return Unsatisfiable
	default:
		return Unknown
	}
}

// UpdateRule updates a named rule in the fixedpoint solver
func (f *Fixedpoint) UpdateRule(rule *Expr, name *Symbol) {
	var namePtr C.Z3_symbol
	if name != nil {
		namePtr = name.ptr
	} else {
		namePtr = nil
	}
	C.Z3_fixedpoint_update_rule(f.ctx.ptr, f.ptr, rule.ptr, namePtr)
}

// GetAnswer retrieves the satisfying instance or instances of solver,
// or definitions for the recursive predicates that show unsatisfiability
func (f *Fixedpoint) GetAnswer() *Expr {
	ptr := C.Z3_fixedpoint_get_answer(f.ctx.ptr, f.ptr)
	if ptr == nil {
		return nil
	}
	return newExpr(f.ctx, ptr)
}

// GetReasonUnknown retrieves explanation why fixedpoint engine returned status Unknown
func (f *Fixedpoint) GetReasonUnknown() string {
	cstr := C.Z3_fixedpoint_get_reason_unknown(f.ctx.ptr, f.ptr)
	return C.GoString(cstr)
}

// GetNumLevels retrieves the number of levels explored for a given predicate
func (f *Fixedpoint) GetNumLevels(predicate *FuncDecl) int {
	return int(C.Z3_fixedpoint_get_num_levels(f.ctx.ptr, f.ptr, predicate.ptr))
}

// GetCoverDelta retrieves the cover delta for a given predicate and level
func (f *Fixedpoint) GetCoverDelta(level int, predicate *FuncDecl) *Expr {
	ptr := C.Z3_fixedpoint_get_cover_delta(f.ctx.ptr, f.ptr, C.int(level), predicate.ptr)
	if ptr == nil {
		return nil
	}
	return newExpr(f.ctx, ptr)
}

// AddCover adds a cover constraint to a predicate at a given level
func (f *Fixedpoint) AddCover(level int, predicate *FuncDecl, property *Expr) {
	C.Z3_fixedpoint_add_cover(f.ctx.ptr, f.ptr, C.int(level), predicate.ptr, property.ptr)
}

// String returns the string representation of the fixedpoint solver
func (f *Fixedpoint) String() string {
	cstr := C.Z3_fixedpoint_to_string(f.ctx.ptr, f.ptr, 0, nil)
	return C.GoString(cstr)
}

// GetStatistics retrieves statistics for the fixedpoint solver
func (f *Fixedpoint) GetStatistics() *Statistics {
	ptr := C.Z3_fixedpoint_get_statistics(f.ctx.ptr, f.ptr)
	return newStatistics(f.ctx, ptr)
}

// GetRules retrieves the current rules as a string
func (f *Fixedpoint) GetRules() string {
	return f.String()
}

// GetAssertions retrieves the fixedpoint assertions as an AST vector
func (f *Fixedpoint) GetAssertions() *ASTVector {
	ptr := C.Z3_fixedpoint_get_assertions(f.ctx.ptr, f.ptr)
	return newASTVector(f.ctx, ptr)
}

// SetPredicateRepresentation sets the predicate representation for a given relation
func (f *Fixedpoint) SetPredicateRepresentation(funcDecl *FuncDecl, kinds []C.Z3_symbol) {
	if len(kinds) == 0 {
		C.Z3_fixedpoint_set_predicate_representation(f.ctx.ptr, f.ptr, funcDecl.ptr, 0, nil)
		return
	}
	C.Z3_fixedpoint_set_predicate_representation(f.ctx.ptr, f.ptr, funcDecl.ptr, C.uint(len(kinds)), &kinds[0])
}

// FromString parses a Datalog program from a string
func (f *Fixedpoint) FromString(s string) {
	cstr := C.CString(s)
	defer C.free(unsafe.Pointer(cstr))
	C.Z3_fixedpoint_from_string(f.ctx.ptr, f.ptr, cstr)
}

// FromFile parses a Datalog program from a file
func (f *Fixedpoint) FromFile(filename string) {
	cstr := C.CString(filename)
	defer C.free(unsafe.Pointer(cstr))
	C.Z3_fixedpoint_from_file(f.ctx.ptr, f.ptr, cstr)
}

// Statistics represents statistics for Z3 solvers
type Statistics struct {
	ctx *Context
	ptr C.Z3_stats
}

// newStatistics creates a new Statistics object with proper memory management
func newStatistics(ctx *Context, ptr C.Z3_stats) *Statistics {
	stats := &Statistics{ctx: ctx, ptr: ptr}
	C.Z3_stats_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(stats, func(s *Statistics) {
		C.Z3_stats_dec_ref(s.ctx.ptr, s.ptr)
	})
	return stats
}

// String returns the string representation of statistics
func (s *Statistics) String() string {
	cstr := C.Z3_stats_to_string(s.ctx.ptr, s.ptr)
	return C.GoString(cstr)
}

// Size returns the number of statistical data entries
func (s *Statistics) Size() int {
	return int(C.Z3_stats_size(s.ctx.ptr, s.ptr))
}

// GetKey returns the key (name) of a statistical data entry at the given index
func (s *Statistics) GetKey(idx int) string {
	cstr := C.Z3_stats_get_key(s.ctx.ptr, s.ptr, C.uint(idx))
	return C.GoString(cstr)
}

// IsUint returns true if the statistical data at the given index is unsigned integer
func (s *Statistics) IsUint(idx int) bool {
	return bool(C.Z3_stats_is_uint(s.ctx.ptr, s.ptr, C.uint(idx)))
}

// IsDouble returns true if the statistical data at the given index is double
func (s *Statistics) IsDouble(idx int) bool {
	return bool(C.Z3_stats_is_double(s.ctx.ptr, s.ptr, C.uint(idx)))
}

// GetUintValue returns the unsigned integer value at the given index
func (s *Statistics) GetUintValue(idx int) uint64 {
	return uint64(C.Z3_stats_get_uint_value(s.ctx.ptr, s.ptr, C.uint(idx)))
}

// GetDoubleValue returns the double value at the given index
func (s *Statistics) GetDoubleValue(idx int) float64 {
	return float64(C.Z3_stats_get_double_value(s.ctx.ptr, s.ptr, C.uint(idx)))
}
