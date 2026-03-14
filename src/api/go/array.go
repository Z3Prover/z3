package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"

// Array operations and sorts

// MkArraySort creates an array sort.
func (c *Context) MkArraySort(domain, range_ *Sort) *Sort {
	return newSort(c, C.Z3_mk_array_sort(c.ptr, domain.ptr, range_.ptr))
}

// MkSelect creates an array read (select) operation.
func (c *Context) MkSelect(array, index *Expr) *Expr {
	return newExpr(c, C.Z3_mk_select(c.ptr, array.ptr, index.ptr))
}

// MkStore creates an array write (store) operation.
func (c *Context) MkStore(array, index, value *Expr) *Expr {
	return newExpr(c, C.Z3_mk_store(c.ptr, array.ptr, index.ptr, value.ptr))
}

// MkConstArray creates a constant array.
func (c *Context) MkConstArray(sort *Sort, value *Expr) *Expr {
	return newExpr(c, C.Z3_mk_const_array(c.ptr, sort.ptr, value.ptr))
}

// MkSelectN creates a multi-index array read (select) operation.
func (c *Context) MkSelectN(array *Expr, indices []*Expr) *Expr {
	idxs := make([]C.Z3_ast, len(indices))
	for i, idx := range indices {
		idxs[i] = idx.ptr
	}
	var idxsPtr *C.Z3_ast
	if len(idxs) > 0 {
		idxsPtr = &idxs[0]
	}
	return newExpr(c, C.Z3_mk_select_n(c.ptr, array.ptr, C.uint(len(idxs)), idxsPtr))
}

// MkStoreN creates a multi-index array write (store) operation.
func (c *Context) MkStoreN(array *Expr, indices []*Expr, value *Expr) *Expr {
	idxs := make([]C.Z3_ast, len(indices))
	for i, idx := range indices {
		idxs[i] = idx.ptr
	}
	var idxsPtr *C.Z3_ast
	if len(idxs) > 0 {
		idxsPtr = &idxs[0]
	}
	return newExpr(c, C.Z3_mk_store_n(c.ptr, array.ptr, C.uint(len(idxs)), idxsPtr, value.ptr))
}

// MkArrayDefault returns the default value of an array.
func (c *Context) MkArrayDefault(array *Expr) *Expr {
	return newExpr(c, C.Z3_mk_array_default(c.ptr, array.ptr))
}

// MkArrayExt returns the extensionality witness for two arrays.
// Two arrays are equal if and only if they are equal on the index returned by MkArrayExt.
func (c *Context) MkArrayExt(a1, a2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_array_ext(c.ptr, a1.ptr, a2.ptr))
}

// MkAsArray creates an array from a function declaration.
// The resulting array maps each input to the output of the function.
func (c *Context) MkAsArray(f *FuncDecl) *Expr {
	return newExpr(c, C.Z3_mk_as_array(c.ptr, f.ptr))
}

// MkMap applies a function to the elements of one or more arrays, returning a new array.
// The function f is applied element-wise to the given arrays.
func (c *Context) MkMap(f *FuncDecl, arrays ...*Expr) *Expr {
	cArrays := make([]C.Z3_ast, len(arrays))
	for i, a := range arrays {
		cArrays[i] = a.ptr
	}
	var cArraysPtr *C.Z3_ast
	if len(cArrays) > 0 {
		cArraysPtr = &cArrays[0]
	}
	return newExpr(c, C.Z3_mk_map(c.ptr, f.ptr, C.uint(len(arrays)), cArraysPtr))
}
