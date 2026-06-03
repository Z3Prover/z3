package z3

/*
#include "z3.h"
*/
import "C"

// Special relation constructors

// MkLinearOrder creates a linear (total) order relation over the given sort.
// The id parameter distinguishes multiple linear orders over the same sort.
func (c *Context) MkLinearOrder(s *Sort, id uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_mk_linear_order(c.ptr, s.ptr, C.uint(id)))
}

// MkPartialOrder creates a partial order relation over the given sort.
// The id parameter distinguishes multiple partial orders over the same sort.
func (c *Context) MkPartialOrder(s *Sort, id uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_mk_partial_order(c.ptr, s.ptr, C.uint(id)))
}

// MkPiecewiseLinearOrder creates a piecewise linear order relation over the given sort.
// The id parameter distinguishes multiple piecewise linear orders over the same sort.
func (c *Context) MkPiecewiseLinearOrder(s *Sort, id uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_mk_piecewise_linear_order(c.ptr, s.ptr, C.uint(id)))
}

// MkTreeOrder creates a tree order relation over the given sort.
// The id parameter distinguishes multiple tree orders over the same sort.
func (c *Context) MkTreeOrder(s *Sort, id uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_mk_tree_order(c.ptr, s.ptr, C.uint(id)))
}

// MkTransitiveClosure creates the transitive closure of a binary relation.
// The resulting relation is recursive.
func (c *Context) MkTransitiveClosure(f *FuncDecl) *FuncDecl {
	return newFuncDecl(c, C.Z3_mk_transitive_closure(c.ptr, f.ptr))
}
