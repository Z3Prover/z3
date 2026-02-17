package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"

// Bit-vector operations

// MkBVConst creates a bit-vector constant with the given name and size.
func (c *Context) MkBVConst(name string, size uint) *Expr {
	sym := c.MkStringSymbol(name)
	return c.MkConst(sym, c.MkBvSort(size))
}

// MkBV creates a bit-vector numeral from an integer.
func (c *Context) MkBV(value int, size uint) *Expr {
	return newExpr(c, C.Z3_mk_int(c.ptr, C.int(value), c.MkBvSort(size).ptr))
}

// MkBVFromInt64 creates a bit-vector from an int64.
func (c *Context) MkBVFromInt64(value int64, size uint) *Expr {
	return newExpr(c, C.Z3_mk_int64(c.ptr, C.int64_t(value), c.MkBvSort(size).ptr))
}

// MkBVAdd creates a bit-vector addition.
func (c *Context) MkBVAdd(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvadd(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSub creates a bit-vector subtraction.
func (c *Context) MkBVSub(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsub(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVMul creates a bit-vector multiplication.
func (c *Context) MkBVMul(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvmul(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVUDiv creates an unsigned bit-vector division.
func (c *Context) MkBVUDiv(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvudiv(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSDiv creates a signed bit-vector division.
func (c *Context) MkBVSDiv(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsdiv(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVURem creates an unsigned bit-vector remainder.
func (c *Context) MkBVURem(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvurem(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSRem creates a signed bit-vector remainder.
func (c *Context) MkBVSRem(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsrem(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVNeg creates a bit-vector negation.
func (c *Context) MkBVNeg(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvneg(c.ptr, expr.ptr))
}

// MkBVAnd creates a bit-vector bitwise AND.
func (c *Context) MkBVAnd(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvand(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVOr creates a bit-vector bitwise OR.
func (c *Context) MkBVOr(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvor(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVXor creates a bit-vector bitwise XOR.
func (c *Context) MkBVXor(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvxor(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVNot creates a bit-vector bitwise NOT.
func (c *Context) MkBVNot(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvnot(c.ptr, expr.ptr))
}

// MkBVShl creates a bit-vector shift left.
func (c *Context) MkBVShl(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvshl(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVLShr creates a bit-vector logical shift right.
func (c *Context) MkBVLShr(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvlshr(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVAShr creates a bit-vector arithmetic shift right.
func (c *Context) MkBVAShr(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvashr(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVULT creates an unsigned bit-vector less-than.
func (c *Context) MkBVULT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvult(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSLT creates a signed bit-vector less-than.
func (c *Context) MkBVSLT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvslt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVULE creates an unsigned bit-vector less-than-or-equal.
func (c *Context) MkBVULE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvule(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSLE creates a signed bit-vector less-than-or-equal.
func (c *Context) MkBVSLE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsle(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVUGE creates an unsigned bit-vector greater-than-or-equal.
func (c *Context) MkBVUGE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvuge(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSGE creates a signed bit-vector greater-than-or-equal.
func (c *Context) MkBVSGE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsge(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVUGT creates an unsigned bit-vector greater-than.
func (c *Context) MkBVUGT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvugt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkBVSGT creates a signed bit-vector greater-than.
func (c *Context) MkBVSGT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_bvsgt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkConcat creates a bit-vector concatenation.
func (c *Context) MkConcat(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_concat(c.ptr, lhs.ptr, rhs.ptr))
}

// MkExtract creates a bit-vector extraction.
func (c *Context) MkExtract(high, low uint, expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_extract(c.ptr, C.uint(high), C.uint(low), expr.ptr))
}

// MkSignExt creates a bit-vector sign extension.
func (c *Context) MkSignExt(i uint, expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_sign_ext(c.ptr, C.uint(i), expr.ptr))
}

// MkZeroExt creates a bit-vector zero extension.
func (c *Context) MkZeroExt(i uint, expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_zero_ext(c.ptr, C.uint(i), expr.ptr))
}
