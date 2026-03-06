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
