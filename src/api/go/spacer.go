// Copyright (c) Microsoft Corporation 2025
// Z3 Go API: Spacer quantifier elimination and model projection functions

package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import "runtime"

// ASTMap represents a mapping from Z3 ASTs to Z3 ASTs.
type ASTMap struct {
	ctx *Context
	ptr C.Z3_ast_map
}

// newASTMap creates a new ASTMap and manages its reference count.
func newASTMap(ctx *Context, ptr C.Z3_ast_map) *ASTMap {
	m := &ASTMap{ctx: ctx, ptr: ptr}
	C.Z3_ast_map_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(m, func(am *ASTMap) {
		C.Z3_ast_map_dec_ref(am.ctx.ptr, am.ptr)
	})
	return m
}

// MkASTMap creates a new empty AST map.
func (c *Context) MkASTMap() *ASTMap {
	return newASTMap(c, C.Z3_mk_ast_map(c.ptr))
}

// Contains returns true if the map contains the key k.
func (m *ASTMap) Contains(k *Expr) bool {
	return bool(C.Z3_ast_map_contains(m.ctx.ptr, m.ptr, k.ptr))
}

// Find returns the value associated with key k.
func (m *ASTMap) Find(k *Expr) *Expr {
	return newExpr(m.ctx, C.Z3_ast_map_find(m.ctx.ptr, m.ptr, k.ptr))
}

// Insert associates key k with value v in the map.
func (m *ASTMap) Insert(k, v *Expr) {
	C.Z3_ast_map_insert(m.ctx.ptr, m.ptr, k.ptr, v.ptr)
}

// Erase removes the entry with key k from the map.
func (m *ASTMap) Erase(k *Expr) {
	C.Z3_ast_map_erase(m.ctx.ptr, m.ptr, k.ptr)
}

// Reset removes all entries from the map.
func (m *ASTMap) Reset() {
	C.Z3_ast_map_reset(m.ctx.ptr, m.ptr)
}

// Size returns the number of entries in the map.
func (m *ASTMap) Size() uint {
	return uint(C.Z3_ast_map_size(m.ctx.ptr, m.ptr))
}

// Keys returns all keys in the map as an ASTVector.
func (m *ASTMap) Keys() *ASTVector {
	return newASTVector(m.ctx, C.Z3_ast_map_keys(m.ctx.ptr, m.ptr))
}

// String returns the string representation of the map.
func (m *ASTMap) String() string {
	return C.GoString(C.Z3_ast_map_to_string(m.ctx.ptr, m.ptr))
}

// ModelExtrapolate extrapolates a model of a formula.
// Given a model m and formula fml, returns an expression that is implied by fml
// and is consistent with the model. This is a Spacer-specific function.
func (c *Context) ModelExtrapolate(m *Model, fml *Expr) *Expr {
	return newExpr(c, C.Z3_model_extrapolate(c.ptr, m.ptr, fml.ptr))
}

// QeLite performs best-effort quantifier elimination.
// vars is a vector of variables to eliminate, body is the formula.
func (c *Context) QeLite(vars *ASTVector, body *Expr) *Expr {
	return newExpr(c, C.Z3_qe_lite(c.ptr, vars.ptr, body.ptr))
}

// QeModelProject projects variables given a model.
// bound is a slice of application expressions representing the variables to project.
func (c *Context) QeModelProject(m *Model, bound []*Expr, body *Expr) *Expr {
	n := len(bound)
	cBound := make([]C.Z3_app, n)
	for i, b := range bound {
		cBound[i] = C.Z3_to_app(c.ptr, b.ptr)
	}
	var boundPtr *C.Z3_app
	if n > 0 {
		boundPtr = &cBound[0]
	}
	return newExpr(c, C.Z3_qe_model_project(c.ptr, m.ptr, C.uint(n), boundPtr, body.ptr))
}

// QeModelProjectSkolem projects variables given a model, storing the skolem witnesses in map_.
// bound is a slice of application expressions representing the variables to project.
func (c *Context) QeModelProjectSkolem(m *Model, bound []*Expr, body *Expr, map_ *ASTMap) *Expr {
	n := len(bound)
	cBound := make([]C.Z3_app, n)
	for i, b := range bound {
		cBound[i] = C.Z3_to_app(c.ptr, b.ptr)
	}
	var boundPtr *C.Z3_app
	if n > 0 {
		boundPtr = &cBound[0]
	}
	return newExpr(c, C.Z3_qe_model_project_skolem(c.ptr, m.ptr, C.uint(n), boundPtr, body.ptr, map_.ptr))
}

// QeModelProjectWithWitness projects variables given a model and extracts witnesses.
// The map_ is populated with bindings of projected variables to witness terms.
// bound is a slice of application expressions representing the variables to project.
func (c *Context) QeModelProjectWithWitness(m *Model, bound []*Expr, body *Expr, map_ *ASTMap) *Expr {
	n := len(bound)
	cBound := make([]C.Z3_app, n)
	for i, b := range bound {
		cBound[i] = C.Z3_to_app(c.ptr, b.ptr)
	}
	var boundPtr *C.Z3_app
	if n > 0 {
		boundPtr = &cBound[0]
	}
	return newExpr(c, C.Z3_qe_model_project_with_witness(c.ptr, m.ptr, C.uint(n), boundPtr, body.ptr, map_.ptr))
}
