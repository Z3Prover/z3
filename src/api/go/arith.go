package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"

// Arithmetic operations and sorts

// MkIntSort creates the integer sort.
func (c *Context) MkIntSort() *Sort {
	return newSort(c, C.Z3_mk_int_sort(c.ptr))
}

// MkRealSort creates the real number sort.
func (c *Context) MkRealSort() *Sort {
	return newSort(c, C.Z3_mk_real_sort(c.ptr))
}

// MkInt creates an integer constant from an int.
func (c *Context) MkInt(value int, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_int(c.ptr, C.int(value), sort.ptr))
}

// MkInt64 creates an integer constant from an int64.
func (c *Context) MkInt64(value int64, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_int64(c.ptr, C.int64_t(value), sort.ptr))
}

// MkReal creates a real constant from numerator and denominator.
func (c *Context) MkReal(num, den int) *Expr {
	return newExpr(c, C.Z3_mk_real(c.ptr, C.int(num), C.int(den)))
}

// MkIntConst creates an integer constant (variable) with the given name.
func (c *Context) MkIntConst(name string) *Expr {
	sym := c.MkStringSymbol(name)
	return c.MkConst(sym, c.MkIntSort())
}

// MkRealConst creates a real constant (variable) with the given name.
func (c *Context) MkRealConst(name string) *Expr {
	sym := c.MkStringSymbol(name)
	return c.MkConst(sym, c.MkRealSort())
}

// MkAdd creates an addition.
func (c *Context) MkAdd(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return c.MkInt(0, c.MkIntSort())
	}
	if len(exprs) == 1 {
		return exprs[0]
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_add(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkSub creates a subtraction.
func (c *Context) MkSub(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return c.MkInt(0, c.MkIntSort())
	}
	if len(exprs) == 1 {
		return newExpr(c, C.Z3_mk_unary_minus(c.ptr, exprs[0].ptr))
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_sub(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkMul creates a multiplication.
func (c *Context) MkMul(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return c.MkInt(1, c.MkIntSort())
	}
	if len(exprs) == 1 {
		return exprs[0]
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_mul(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkDiv creates a division.
func (c *Context) MkDiv(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_div(c.ptr, lhs.ptr, rhs.ptr))
}

// MkMod creates a modulo operation.
func (c *Context) MkMod(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_mod(c.ptr, lhs.ptr, rhs.ptr))
}

// MkRem creates a remainder operation.
func (c *Context) MkRem(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_rem(c.ptr, lhs.ptr, rhs.ptr))
}

// MkLt creates a less-than constraint.
func (c *Context) MkLt(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_lt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkLe creates a less-than-or-equal constraint.
func (c *Context) MkLe(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_le(c.ptr, lhs.ptr, rhs.ptr))
}

// MkGt creates a greater-than constraint.
func (c *Context) MkGt(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_gt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkGe creates a greater-than-or-equal constraint.
func (c *Context) MkGe(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_ge(c.ptr, lhs.ptr, rhs.ptr))
}
