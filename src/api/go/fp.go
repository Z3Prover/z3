package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"unsafe"
)

// Floating-point operations

// MkFPSort creates a floating-point sort.
func (c *Context) MkFPSort(ebits, sbits uint) *Sort {
	return newSort(c, C.Z3_mk_fpa_sort(c.ptr, C.uint(ebits), C.uint(sbits)))
}

// MkFPSort16 creates a 16-bit floating-point sort.
func (c *Context) MkFPSort16() *Sort {
	return newSort(c, C.Z3_mk_fpa_sort_16(c.ptr))
}

// MkFPSort32 creates a 32-bit floating-point sort (single precision).
func (c *Context) MkFPSort32() *Sort {
	return newSort(c, C.Z3_mk_fpa_sort_32(c.ptr))
}

// MkFPSort64 creates a 64-bit floating-point sort (double precision).
func (c *Context) MkFPSort64() *Sort {
	return newSort(c, C.Z3_mk_fpa_sort_64(c.ptr))
}

// MkFPSort128 creates a 128-bit floating-point sort (quadruple precision).
func (c *Context) MkFPSort128() *Sort {
	return newSort(c, C.Z3_mk_fpa_sort_128(c.ptr))
}

// MkFPRoundingModeSort creates the rounding mode sort.
func (c *Context) MkFPRoundingModeSort() *Sort {
	return newSort(c, C.Z3_mk_fpa_rounding_mode_sort(c.ptr))
}

// MkFPNumeral creates a floating-point numeral from a string.
func (c *Context) MkFPNumeral(value string, sort *Sort) *Expr {
	cStr := C.CString(value)
	defer C.free(unsafe.Pointer(cStr))
	return newExpr(c, C.Z3_mk_numeral(c.ptr, cStr, sort.ptr))
}

// MkFPInf creates a floating-point infinity.
func (c *Context) MkFPInf(sort *Sort, negative bool) *Expr {
	return newExpr(c, C.Z3_mk_fpa_inf(c.ptr, sort.ptr, C.bool(negative)))
}

// MkFPNaN creates a floating-point NaN.
func (c *Context) MkFPNaN(sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_nan(c.ptr, sort.ptr))
}

// MkFPZero creates a floating-point zero.
func (c *Context) MkFPZero(sort *Sort, negative bool) *Expr {
	return newExpr(c, C.Z3_mk_fpa_zero(c.ptr, sort.ptr, C.bool(negative)))
}

// MkFPAdd creates a floating-point addition.
func (c *Context) MkFPAdd(rm, lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_add(c.ptr, rm.ptr, lhs.ptr, rhs.ptr))
}

// MkFPSub creates a floating-point subtraction.
func (c *Context) MkFPSub(rm, lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_sub(c.ptr, rm.ptr, lhs.ptr, rhs.ptr))
}

// MkFPMul creates a floating-point multiplication.
func (c *Context) MkFPMul(rm, lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_mul(c.ptr, rm.ptr, lhs.ptr, rhs.ptr))
}

// MkFPDiv creates a floating-point division.
func (c *Context) MkFPDiv(rm, lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_div(c.ptr, rm.ptr, lhs.ptr, rhs.ptr))
}

// MkFPNeg creates a floating-point negation.
func (c *Context) MkFPNeg(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_neg(c.ptr, expr.ptr))
}

// MkFPAbs creates a floating-point absolute value.
func (c *Context) MkFPAbs(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_abs(c.ptr, expr.ptr))
}

// MkFPSqrt creates a floating-point square root.
func (c *Context) MkFPSqrt(rm, expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_sqrt(c.ptr, rm.ptr, expr.ptr))
}

// MkFPLT creates a floating-point less-than.
func (c *Context) MkFPLT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_lt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkFPGT creates a floating-point greater-than.
func (c *Context) MkFPGT(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_gt(c.ptr, lhs.ptr, rhs.ptr))
}

// MkFPLE creates a floating-point less-than-or-equal.
func (c *Context) MkFPLE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_leq(c.ptr, lhs.ptr, rhs.ptr))
}

// MkFPGE creates a floating-point greater-than-or-equal.
func (c *Context) MkFPGE(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_geq(c.ptr, lhs.ptr, rhs.ptr))
}

// MkFPEq creates a floating-point equality.
func (c *Context) MkFPEq(lhs, rhs *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_eq(c.ptr, lhs.ptr, rhs.ptr))
}

// MkFPIsNaN creates a predicate checking if a floating-point number is NaN.
func (c *Context) MkFPIsNaN(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_nan(c.ptr, expr.ptr))
}

// MkFPIsInf creates a predicate checking if a floating-point number is infinite.
func (c *Context) MkFPIsInf(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_infinite(c.ptr, expr.ptr))
}

// MkFPIsZero creates a predicate checking if a floating-point number is zero.
func (c *Context) MkFPIsZero(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_zero(c.ptr, expr.ptr))
}
