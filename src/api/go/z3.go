// Package z3 provides Go bindings for the Z3 theorem prover.
//
// Z3 is a high-performance SMT (Satisfiability Modulo Theories) solver
// developed at Microsoft Research. These bindings wrap the Z3 C API using
// CGO and provide idiomatic Go interfaces with automatic memory management.
//
// # Basic Usage
//
// Create a context and solver:
//
//	ctx := z3.NewContext()
//	solver := ctx.NewSolver()
//
// Create variables and constraints:
//
//	x := ctx.MkIntConst("x")
//	y := ctx.MkIntConst("y")
//	solver.Assert(ctx.MkEq(ctx.MkAdd(x, y), ctx.MkInt(10, ctx.MkIntSort())))
//	solver.Assert(ctx.MkGt(x, y))
//
// Check satisfiability and get model:
//
//	if solver.Check() == z3.Satisfiable {
//	    model := solver.Model()
//	    xVal, _ := model.Eval(x, true)
//	    fmt.Println("x =", xVal.String())
//	}
//
// # Memory Management
//
// All Z3 objects are automatically managed using Go finalizers. Reference
// counting is handled transparently - you don't need to manually free objects.
//
// # Supported Features
//
//   - Boolean logic, integer and real arithmetic
//   - Bit-vectors and floating-point arithmetic
//   - Arrays, sequences, and strings
//   - Regular expressions
//   - Algebraic datatypes
//   - Quantifiers and lambda expressions
//   - Tactics and goal-based solving
//   - Optimization (MaxSMT)
//   - Fixedpoint solver (Datalog/CHC)
//
// For more examples, see the examples/go directory in the Z3 repository.
package z3

/*
#cgo CFLAGS: -I${SRCDIR}/..
#cgo LDFLAGS: -lz3
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"runtime"
	"unsafe"
)

// Config represents a Z3 configuration object.
type Config struct {
	ptr C.Z3_config
}

// NewConfig creates a new Z3 configuration.
func NewConfig() *Config {
	cfg := &Config{ptr: C.Z3_mk_config()}
	runtime.SetFinalizer(cfg, func(c *Config) {
		C.Z3_del_config(c.ptr)
	})
	return cfg
}

// SetParamValue sets a configuration parameter.
func (c *Config) SetParamValue(paramID, paramValue string) {
	cParamID := C.CString(paramID)
	cParamValue := C.CString(paramValue)
	defer C.free(unsafe.Pointer(cParamID))
	defer C.free(unsafe.Pointer(cParamValue))
	C.Z3_set_param_value(c.ptr, cParamID, cParamValue)
}

// Context represents a Z3 logical context.
type Context struct {
	ptr C.Z3_context
}

// NewContext creates a new Z3 context with default configuration.
func NewContext() *Context {
	ctx := &Context{ptr: C.Z3_mk_context_rc(C.Z3_mk_config())}
	runtime.SetFinalizer(ctx, func(c *Context) {
		C.Z3_del_context(c.ptr)
	})
	return ctx
}

// NewContextWithConfig creates a new Z3 context with the given configuration.
func NewContextWithConfig(cfg *Config) *Context {
	ctx := &Context{ptr: C.Z3_mk_context_rc(cfg.ptr)}
	runtime.SetFinalizer(ctx, func(c *Context) {
		C.Z3_del_context(c.ptr)
	})
	return ctx
}

// SetParam sets a global or context parameter.
func (c *Context) SetParam(key, value string) {
	cKey := C.CString(key)
	cValue := C.CString(value)
	defer C.free(unsafe.Pointer(cKey))
	defer C.free(unsafe.Pointer(cValue))
	C.Z3_update_param_value(c.ptr, cKey, cValue)
}

// Symbol represents a Z3 symbol.
type Symbol struct {
	ctx *Context
	ptr C.Z3_symbol
}

// newSymbol creates a new Symbol.
func newSymbol(ctx *Context, ptr C.Z3_symbol) *Symbol {
	return &Symbol{ctx: ctx, ptr: ptr}
}

// MkIntSymbol creates an integer symbol.
func (c *Context) MkIntSymbol(i int) *Symbol {
	return &Symbol{
		ctx: c,
		ptr: C.Z3_mk_int_symbol(c.ptr, C.int(i)),
	}
}

// MkStringSymbol creates a string symbol.
func (c *Context) MkStringSymbol(s string) *Symbol {
	cStr := C.CString(s)
	defer C.free(unsafe.Pointer(cStr))
	return &Symbol{
		ctx: c,
		ptr: C.Z3_mk_string_symbol(c.ptr, cStr),
	}
}

// String returns the string representation of the symbol.
func (s *Symbol) String() string {
	kind := C.Z3_get_symbol_kind(s.ctx.ptr, s.ptr)
	if kind == C.Z3_INT_SYMBOL {
		return string(rune(C.Z3_get_symbol_int(s.ctx.ptr, s.ptr)))
	}
	return C.GoString(C.Z3_get_symbol_string(s.ctx.ptr, s.ptr))
}

// AST represents a Z3 abstract syntax tree node.
type AST struct {
	ctx *Context
	ptr C.Z3_ast
}

// incRef increments the reference count of the AST.
func (a *AST) incRef() {
	C.Z3_inc_ref(a.ctx.ptr, a.ptr)
}

// decRef decrements the reference count of the AST.
func (a *AST) decRef() {
	C.Z3_dec_ref(a.ctx.ptr, a.ptr)
}

// String returns the string representation of the AST.
func (a *AST) String() string {
	return C.GoString(C.Z3_ast_to_string(a.ctx.ptr, a.ptr))
}

// Hash returns the hash code of the AST.
func (a *AST) Hash() uint32 {
	return uint32(C.Z3_get_ast_hash(a.ctx.ptr, a.ptr))
}

// Equal checks if two ASTs are equal.
func (a *AST) Equal(other *AST) bool {
	if a.ctx != other.ctx {
		return false
	}
	return bool(C.Z3_is_eq_ast(a.ctx.ptr, a.ptr, other.ptr))
}

// Sort represents a Z3 sort (type).
type Sort struct {
	ctx *Context
	ptr C.Z3_sort
}

// newSort creates a new Sort and manages its reference count.
func newSort(ctx *Context, ptr C.Z3_sort) *Sort {
	sort := &Sort{ctx: ctx, ptr: ptr}
	C.Z3_inc_ref(ctx.ptr, C.Z3_sort_to_ast(ctx.ptr, ptr))
	runtime.SetFinalizer(sort, func(s *Sort) {
		C.Z3_dec_ref(s.ctx.ptr, C.Z3_sort_to_ast(s.ctx.ptr, s.ptr))
	})
	return sort
}

// String returns the string representation of the sort.
func (s *Sort) String() string {
	return C.GoString(C.Z3_sort_to_string(s.ctx.ptr, s.ptr))
}

// Equal checks if two sorts are equal.
func (s *Sort) Equal(other *Sort) bool {
	if s.ctx != other.ctx {
		return false
	}
	return bool(C.Z3_is_eq_sort(s.ctx.ptr, s.ptr, other.ptr))
}

// MkBoolSort creates the Boolean sort.
func (c *Context) MkBoolSort() *Sort {
	return newSort(c, C.Z3_mk_bool_sort(c.ptr))
}

// MkBvSort creates a bit-vector sort of the given size.
func (c *Context) MkBvSort(sz uint) *Sort {
	return newSort(c, C.Z3_mk_bv_sort(c.ptr, C.uint(sz)))
}

// Expr represents a Z3 expression.
type Expr struct {
	ctx *Context
	ptr C.Z3_ast
}

// newExpr creates a new Expr and manages its reference count.
func newExpr(ctx *Context, ptr C.Z3_ast) *Expr {
	expr := &Expr{ctx: ctx, ptr: ptr}
	C.Z3_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(expr, func(e *Expr) {
		C.Z3_dec_ref(e.ctx.ptr, e.ptr)
	})
	return expr
}

// String returns the string representation of the expression.
func (e *Expr) String() string {
	return C.GoString(C.Z3_ast_to_string(e.ctx.ptr, e.ptr))
}

// Equal checks if two expressions are equal.
func (e *Expr) Equal(other *Expr) bool {
	if e.ctx != other.ctx {
		return false
	}
	return bool(C.Z3_is_eq_ast(e.ctx.ptr, e.ptr, other.ptr))
}

// GetSort returns the sort of the expression.
func (e *Expr) GetSort() *Sort {
	return newSort(e.ctx, C.Z3_get_sort(e.ctx.ptr, e.ptr))
}

// Pattern represents a Z3 pattern for quantifier instantiation.
type Pattern struct {
	ctx *Context
	ptr C.Z3_pattern
}

// newPattern creates a new Pattern and manages its reference count.
func newPattern(ctx *Context, ptr C.Z3_pattern) *Pattern {
	p := &Pattern{ctx: ctx, ptr: ptr}
	// Patterns are ASTs in the C API
	C.Z3_inc_ref(ctx.ptr, (C.Z3_ast)(unsafe.Pointer(ptr)))
	runtime.SetFinalizer(p, func(pat *Pattern) {
		C.Z3_dec_ref(pat.ctx.ptr, (C.Z3_ast)(unsafe.Pointer(pat.ptr)))
	})
	return p
}

// ASTVector represents a vector of Z3 ASTs.
type ASTVector struct {
	ctx *Context
	ptr C.Z3_ast_vector
}

// newASTVector creates a new ASTVector and manages its reference count.
func newASTVector(ctx *Context, ptr C.Z3_ast_vector) *ASTVector {
	v := &ASTVector{ctx: ctx, ptr: ptr}
	C.Z3_ast_vector_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(v, func(vec *ASTVector) {
		C.Z3_ast_vector_dec_ref(vec.ctx.ptr, vec.ptr)
	})
	return v
}

// ParamDescrs represents parameter descriptions for Z3 objects.
type ParamDescrs struct {
	ctx *Context
	ptr C.Z3_param_descrs
}

// newParamDescrs creates a new ParamDescrs and manages its reference count.
func newParamDescrs(ctx *Context, ptr C.Z3_param_descrs) *ParamDescrs {
	pd := &ParamDescrs{ctx: ctx, ptr: ptr}
	C.Z3_param_descrs_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(pd, func(descrs *ParamDescrs) {
		C.Z3_param_descrs_dec_ref(descrs.ctx.ptr, descrs.ptr)
	})
	return pd
}

// MkTrue creates the Boolean constant true.
func (c *Context) MkTrue() *Expr {
	return newExpr(c, C.Z3_mk_true(c.ptr))
}

// MkFalse creates the Boolean constant false.
func (c *Context) MkFalse() *Expr {
	return newExpr(c, C.Z3_mk_false(c.ptr))
}

// MkBool creates a Boolean constant.
func (c *Context) MkBool(value bool) *Expr {
	if value {
		return c.MkTrue()
	}
	return c.MkFalse()
}

// MkNumeral creates a numeral from a string.
func (c *Context) MkNumeral(numeral string, sort *Sort) *Expr {
	cStr := C.CString(numeral)
	defer C.free(unsafe.Pointer(cStr))
	return newExpr(c, C.Z3_mk_numeral(c.ptr, cStr, sort.ptr))
}

// MkConst creates a constant (variable) with the given name and sort.
func (c *Context) MkConst(name *Symbol, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_const(c.ptr, name.ptr, sort.ptr))
}

// MkBoolConst creates a Boolean constant (variable) with the given name.
func (c *Context) MkBoolConst(name string) *Expr {
	sym := c.MkStringSymbol(name)
	return c.MkConst(sym, c.MkBoolSort())
}

// Boolean operations

// MkAnd creates a conjunction.
func (c *Context) MkAnd(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return c.MkTrue()
	}
	if len(exprs) == 1 {
		return exprs[0]
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_and(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkOr creates a disjunction.
func (c *Context) MkOr(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return c.MkFalse()
	}
	if len(exprs) == 1 {
		return exprs[0]
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_or(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkNot creates a negation.
func (c *Context) MkNot(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_not(c.ptr, expr.ptr))
}

// MkImplies creates an implication.
func (c *Context) MkImplies(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_implies(c.ptr, lhs.ptr, rhs.ptr))
}

// MkIff creates a bi-implication (if and only if).
func (c *Context) MkIff(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_iff(c.ptr, lhs.ptr, rhs.ptr))
}

// MkXor creates exclusive or.
func (c *Context) MkXor(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_xor(c.ptr, lhs.ptr, rhs.ptr))
}

// Comparison operations

// MkEq creates an equality.
func (c *Context) MkEq(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_eq(c.ptr, lhs.ptr, rhs.ptr))
}

// MkDistinct creates a distinct constraint.
func (c *Context) MkDistinct(exprs ...*Expr) *Expr {
	if len(exprs) <= 1 {
		return c.MkTrue()
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_distinct(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// FuncDecl represents a function declaration.
type FuncDecl struct {
	ctx *Context
	ptr C.Z3_func_decl
}

// newFuncDecl creates a new FuncDecl and manages its reference count.
func newFuncDecl(ctx *Context, ptr C.Z3_func_decl) *FuncDecl {
	fd := &FuncDecl{ctx: ctx, ptr: ptr}
	C.Z3_inc_ref(ctx.ptr, C.Z3_func_decl_to_ast(ctx.ptr, ptr))
	runtime.SetFinalizer(fd, func(f *FuncDecl) {
		C.Z3_dec_ref(f.ctx.ptr, C.Z3_func_decl_to_ast(f.ctx.ptr, f.ptr))
	})
	return fd
}

// String returns the string representation of the function declaration.
func (f *FuncDecl) String() string {
	return C.GoString(C.Z3_func_decl_to_string(f.ctx.ptr, f.ptr))
}

// GetName returns the name of the function declaration.
func (f *FuncDecl) GetName() *Symbol {
	return &Symbol{
		ctx: f.ctx,
		ptr: C.Z3_get_decl_name(f.ctx.ptr, f.ptr),
	}
}

// GetArity returns the arity (number of parameters) of the function.
func (f *FuncDecl) GetArity() int {
	return int(C.Z3_get_arity(f.ctx.ptr, f.ptr))
}

// GetDomain returns the sort of the i-th parameter.
func (f *FuncDecl) GetDomain(i int) *Sort {
	return newSort(f.ctx, C.Z3_get_domain(f.ctx.ptr, f.ptr, C.uint(i)))
}

// GetRange returns the sort of the return value.
func (f *FuncDecl) GetRange() *Sort {
	return newSort(f.ctx, C.Z3_get_range(f.ctx.ptr, f.ptr))
}

// MkFuncDecl creates a function declaration.
func (c *Context) MkFuncDecl(name *Symbol, domain []*Sort, range_ *Sort) *FuncDecl {
	cDomain := make([]C.Z3_sort, len(domain))
	for i, s := range domain {
		cDomain[i] = s.ptr
	}
	var domainPtr *C.Z3_sort
	if len(domain) > 0 {
		domainPtr = &cDomain[0]
	}
	return newFuncDecl(c, C.Z3_mk_func_decl(c.ptr, name.ptr, C.uint(len(domain)), domainPtr, range_.ptr))
}

// MkApp creates a function application.
func (c *Context) MkApp(decl *FuncDecl, args ...*Expr) *Expr {
	cArgs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cArgs[i] = a.ptr
	}
	var argsPtr *C.Z3_ast
	if len(args) > 0 {
		argsPtr = &cArgs[0]
	}
	return newExpr(c, C.Z3_mk_app(c.ptr, decl.ptr, C.uint(len(args)), argsPtr))
}

// Quantifier operations

// MkForall creates a universal quantifier.
func (c *Context) MkForall(bound []*Expr, body *Expr) *Expr {
	cBound := make([]C.Z3_app, len(bound))
	for i, b := range bound {
		// Z3_app is a subtype of Z3_ast; constants are apps
		cBound[i] = (C.Z3_app)(unsafe.Pointer(b.ptr))
	}
	var boundPtr *C.Z3_app
	if len(bound) > 0 {
		boundPtr = &cBound[0]
	}
	return newExpr(c, C.Z3_mk_forall_const(c.ptr, 0, C.uint(len(bound)), boundPtr, 0, nil, body.ptr))
}

// MkExists creates an existential quantifier.
func (c *Context) MkExists(bound []*Expr, body *Expr) *Expr {
	cBound := make([]C.Z3_app, len(bound))
	for i, b := range bound {
		// Z3_app is a subtype of Z3_ast; constants are apps
		cBound[i] = (C.Z3_app)(unsafe.Pointer(b.ptr))
	}
	var boundPtr *C.Z3_app
	if len(bound) > 0 {
		boundPtr = &cBound[0]
	}
	return newExpr(c, C.Z3_mk_exists_const(c.ptr, 0, C.uint(len(bound)), boundPtr, 0, nil, body.ptr))
}

// Simplify simplifies an expression.
func (e *Expr) Simplify() *Expr {
	return newExpr(e.ctx, C.Z3_simplify(e.ctx.ptr, e.ptr))
}

// MkTypeVariable creates a type variable sort for use in polymorphic functions and datatypes
func (c *Context) MkTypeVariable(name *Symbol) *Sort {
	return newSort(c, C.Z3_mk_type_variable(c.ptr, name.ptr))
}

// Quantifier represents a quantified formula (forall or exists)
type Quantifier struct {
	ctx *Context
	ptr C.Z3_ast
}

// newQuantifier creates a new Quantifier with proper memory management
func newQuantifier(ctx *Context, ptr C.Z3_ast) *Quantifier {
	q := &Quantifier{ctx: ctx, ptr: ptr}
	C.Z3_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(q, func(qf *Quantifier) {
		C.Z3_dec_ref(qf.ctx.ptr, qf.ptr)
	})
	return q
}

// AsExpr converts a Quantifier to an Expr
func (q *Quantifier) AsExpr() *Expr {
	return newExpr(q.ctx, q.ptr)
}

// IsUniversal returns true if this is a universal quantifier (forall)
func (q *Quantifier) IsUniversal() bool {
	return bool(C.Z3_is_quantifier_forall(q.ctx.ptr, q.ptr))
}

// IsExistential returns true if this is an existential quantifier (exists)
func (q *Quantifier) IsExistential() bool {
	return bool(C.Z3_is_quantifier_exists(q.ctx.ptr, q.ptr))
}

// GetWeight returns the weight of the quantifier
func (q *Quantifier) GetWeight() int {
	return int(C.Z3_get_quantifier_weight(q.ctx.ptr, q.ptr))
}

// GetNumPatterns returns the number of patterns
func (q *Quantifier) GetNumPatterns() int {
	return int(C.Z3_get_quantifier_num_patterns(q.ctx.ptr, q.ptr))
}

// GetPattern returns the pattern at the given index
func (q *Quantifier) GetPattern(idx int) *Pattern {
	ptr := C.Z3_get_quantifier_pattern_ast(q.ctx.ptr, q.ptr, C.uint(idx))
	return newPattern(q.ctx, ptr)
}

// GetNumNoPatterns returns the number of no-patterns
func (q *Quantifier) GetNumNoPatterns() int {
	return int(C.Z3_get_quantifier_num_no_patterns(q.ctx.ptr, q.ptr))
}

// GetNoPattern returns the no-pattern at the given index
func (q *Quantifier) GetNoPattern(idx int) *Pattern {
	ptr := C.Z3_get_quantifier_no_pattern_ast(q.ctx.ptr, q.ptr, C.uint(idx))
	return newPattern(q.ctx, (C.Z3_pattern)(unsafe.Pointer(ptr)))
}

// GetNumBound returns the number of bound variables
func (q *Quantifier) GetNumBound() int {
	return int(C.Z3_get_quantifier_num_bound(q.ctx.ptr, q.ptr))
}

// GetBoundName returns the name of the bound variable at the given index
func (q *Quantifier) GetBoundName(idx int) *Symbol {
	ptr := C.Z3_get_quantifier_bound_name(q.ctx.ptr, q.ptr, C.uint(idx))
	return newSymbol(q.ctx, ptr)
}

// GetBoundSort returns the sort of the bound variable at the given index
func (q *Quantifier) GetBoundSort(idx int) *Sort {
	ptr := C.Z3_get_quantifier_bound_sort(q.ctx.ptr, q.ptr, C.uint(idx))
	return newSort(q.ctx, ptr)
}

// GetBody returns the body of the quantifier
func (q *Quantifier) GetBody() *Expr {
	ptr := C.Z3_get_quantifier_body(q.ctx.ptr, q.ptr)
	return newExpr(q.ctx, ptr)
}

// String returns the string representation of the quantifier
func (q *Quantifier) String() string {
	return q.AsExpr().String()
}

// MkQuantifier creates a quantifier with patterns
func (c *Context) MkQuantifier(isForall bool, weight int, sorts []*Sort, names []*Symbol, body *Expr, patterns []*Pattern) *Quantifier {
	var forallInt C.bool
	if isForall {
		forallInt = true
	} else {
		forallInt = false
	}

	numBound := len(sorts)
	if numBound != len(names) {
		panic("Number of sorts must match number of names")
	}

	var cSorts []C.Z3_sort
	var cNames []C.Z3_symbol
	if numBound > 0 {
		cSorts = make([]C.Z3_sort, numBound)
		cNames = make([]C.Z3_symbol, numBound)
		for i := 0; i < numBound; i++ {
			cSorts[i] = sorts[i].ptr
			cNames[i] = names[i].ptr
		}
	}

	var cPatterns []C.Z3_pattern
	var patternsPtr *C.Z3_pattern
	numPatterns := len(patterns)
	if numPatterns > 0 {
		cPatterns = make([]C.Z3_pattern, numPatterns)
		for i := 0; i < numPatterns; i++ {
			cPatterns[i] = patterns[i].ptr
		}
		patternsPtr = &cPatterns[0]
	}

	var sortsPtr *C.Z3_sort
	var namesPtr *C.Z3_symbol
	if numBound > 0 {
		sortsPtr = &cSorts[0]
		namesPtr = &cNames[0]
	}

	ptr := C.Z3_mk_quantifier(c.ptr, forallInt, C.uint(weight), C.uint(numPatterns), patternsPtr,
		C.uint(numBound), sortsPtr, namesPtr, body.ptr)
	return newQuantifier(c, ptr)
}

// MkQuantifierConst creates a quantifier using constant bound variables
func (c *Context) MkQuantifierConst(isForall bool, weight int, bound []*Expr, body *Expr, patterns []*Pattern) *Quantifier {
	var forallInt C.bool
	if isForall {
		forallInt = true
	} else {
		forallInt = false
	}

	numBound := len(bound)
	var cBound []C.Z3_app
	var boundPtr *C.Z3_app
	if numBound > 0 {
		cBound = make([]C.Z3_app, numBound)
		for i := 0; i < numBound; i++ {
			cBound[i] = (C.Z3_app)(unsafe.Pointer(bound[i].ptr))
		}
		boundPtr = &cBound[0]
	}

	var cPatterns []C.Z3_pattern
	var patternsPtr *C.Z3_pattern
	numPatterns := len(patterns)
	if numPatterns > 0 {
		cPatterns = make([]C.Z3_pattern, numPatterns)
		for i := 0; i < numPatterns; i++ {
			cPatterns[i] = patterns[i].ptr
		}
		patternsPtr = &cPatterns[0]
	}

	ptr := C.Z3_mk_quantifier_const(c.ptr, forallInt, C.uint(weight), C.uint(numBound), boundPtr,
		C.uint(numPatterns), patternsPtr, body.ptr)
	return newQuantifier(c, ptr)
}

// Lambda represents a lambda expression
type Lambda struct {
	ctx *Context
	ptr C.Z3_ast
}

// newLambda creates a new Lambda with proper memory management
func newLambda(ctx *Context, ptr C.Z3_ast) *Lambda {
	l := &Lambda{ctx: ctx, ptr: ptr}
	C.Z3_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(l, func(lam *Lambda) {
		C.Z3_dec_ref(lam.ctx.ptr, lam.ptr)
	})
	return l
}

// AsExpr converts a Lambda to an Expr
func (l *Lambda) AsExpr() *Expr {
	return newExpr(l.ctx, l.ptr)
}

// GetNumBound returns the number of bound variables
func (l *Lambda) GetNumBound() int {
	return int(C.Z3_get_quantifier_num_bound(l.ctx.ptr, l.ptr))
}

// GetBoundName returns the name of the bound variable at the given index
func (l *Lambda) GetBoundName(idx int) *Symbol {
	ptr := C.Z3_get_quantifier_bound_name(l.ctx.ptr, l.ptr, C.uint(idx))
	return newSymbol(l.ctx, ptr)
}

// GetBoundSort returns the sort of the bound variable at the given index
func (l *Lambda) GetBoundSort(idx int) *Sort {
	ptr := C.Z3_get_quantifier_bound_sort(l.ctx.ptr, l.ptr, C.uint(idx))
	return newSort(l.ctx, ptr)
}

// GetBody returns the body of the lambda expression
func (l *Lambda) GetBody() *Expr {
	ptr := C.Z3_get_quantifier_body(l.ctx.ptr, l.ptr)
	return newExpr(l.ctx, ptr)
}

// String returns the string representation of the lambda
func (l *Lambda) String() string {
	return l.AsExpr().String()
}

// MkLambda creates a lambda expression with sorts and names
func (c *Context) MkLambda(sorts []*Sort, names []*Symbol, body *Expr) *Lambda {
	numBound := len(sorts)
	if numBound != len(names) {
		panic("Number of sorts must match number of names")
	}

	var cSorts []C.Z3_sort
	var cNames []C.Z3_symbol
	var sortsPtr *C.Z3_sort
	var namesPtr *C.Z3_symbol

	if numBound > 0 {
		cSorts = make([]C.Z3_sort, numBound)
		cNames = make([]C.Z3_symbol, numBound)
		for i := 0; i < numBound; i++ {
			cSorts[i] = sorts[i].ptr
			cNames[i] = names[i].ptr
		}
		sortsPtr = &cSorts[0]
		namesPtr = &cNames[0]
	}

	ptr := C.Z3_mk_lambda(c.ptr, C.uint(numBound), sortsPtr, namesPtr, body.ptr)
	return newLambda(c, ptr)
}

// MkLambdaConst creates a lambda expression using constant bound variables
func (c *Context) MkLambdaConst(bound []*Expr, body *Expr) *Lambda {
	numBound := len(bound)
	var cBound []C.Z3_app
	var boundPtr *C.Z3_app

	if numBound > 0 {
		cBound = make([]C.Z3_app, numBound)
		for i := 0; i < numBound; i++ {
			cBound[i] = (C.Z3_app)(unsafe.Pointer(bound[i].ptr))
		}
		boundPtr = &cBound[0]
	}

	ptr := C.Z3_mk_lambda_const(c.ptr, C.uint(numBound), boundPtr, body.ptr)
	return newLambda(c, ptr)
}

// astVectorToExprs converts a Z3_ast_vector to a slice of Expr.
// This function properly manages the reference count of the vector by
// incrementing it on entry and decrementing it on exit.
// The individual AST elements are already reference counted by newExpr.
func astVectorToExprs(ctx *Context, vec C.Z3_ast_vector) []*Expr {
	// Increment reference count for the vector since we're using it
	C.Z3_ast_vector_inc_ref(ctx.ptr, vec)
	defer C.Z3_ast_vector_dec_ref(ctx.ptr, vec)

	size := uint(C.Z3_ast_vector_size(ctx.ptr, vec))
	result := make([]*Expr, size)
	for i := uint(0); i < size; i++ {
		result[i] = newExpr(ctx, C.Z3_ast_vector_get(ctx.ptr, vec, C.uint(i)))
	}
	return result
}
