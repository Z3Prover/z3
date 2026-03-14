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

// MkFPIsNormal creates a predicate checking if a floating-point number is normal.
func (c *Context) MkFPIsNormal(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_normal(c.ptr, expr.ptr))
}

// MkFPIsSubnormal creates a predicate checking if a floating-point number is subnormal.
func (c *Context) MkFPIsSubnormal(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_subnormal(c.ptr, expr.ptr))
}

// MkFPIsNegative creates a predicate checking if a floating-point number is negative.
func (c *Context) MkFPIsNegative(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_negative(c.ptr, expr.ptr))
}

// MkFPIsPositive creates a predicate checking if a floating-point number is positive.
func (c *Context) MkFPIsPositive(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_is_positive(c.ptr, expr.ptr))
}

// MkFPToIEEEBV converts a floating-point number to its IEEE 754 bit-vector representation.
func (c *Context) MkFPToIEEEBV(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_ieee_bv(c.ptr, expr.ptr))
}

// MkFPToReal converts a floating-point number to a real number.
func (c *Context) MkFPToReal(expr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_real(c.ptr, expr.ptr))
}

// MkFPRNE creates the round-nearest-ties-to-even rounding mode.
func (c *Context) MkFPRNE() *Expr {
	return newExpr(c, C.Z3_mk_fpa_rne(c.ptr))
}

// MkFPRNA creates the round-nearest-ties-to-away rounding mode.
func (c *Context) MkFPRNA() *Expr {
	return newExpr(c, C.Z3_mk_fpa_rna(c.ptr))
}

// MkFPRTP creates the round-toward-positive rounding mode.
func (c *Context) MkFPRTP() *Expr {
	return newExpr(c, C.Z3_mk_fpa_rtp(c.ptr))
}

// MkFPRTN creates the round-toward-negative rounding mode.
func (c *Context) MkFPRTN() *Expr {
	return newExpr(c, C.Z3_mk_fpa_rtn(c.ptr))
}

// MkFPRTZ creates the round-toward-zero rounding mode.
func (c *Context) MkFPRTZ() *Expr {
	return newExpr(c, C.Z3_mk_fpa_rtz(c.ptr))
}

// MkFPFP creates a floating-point number from a sign bit (1-bit BV), exponent BV, and significand BV.
func (c *Context) MkFPFP(sgn, exp, sig *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_fp(c.ptr, sgn.ptr, exp.ptr, sig.ptr))
}

// MkFPNumeralFloat creates a floating-point numeral from a float32 value.
func (c *Context) MkFPNumeralFloat(v float32, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_numeral_float(c.ptr, C.float(v), sort.ptr))
}

// MkFPNumeralDouble creates a floating-point numeral from a float64 value.
func (c *Context) MkFPNumeralDouble(v float64, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_numeral_double(c.ptr, C.double(v), sort.ptr))
}

// MkFPNumeralInt creates a floating-point numeral from a signed integer.
func (c *Context) MkFPNumeralInt(v int, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_numeral_int(c.ptr, C.int(v), sort.ptr))
}

// MkFPNumeralIntUint creates a floating-point numeral from a sign, signed exponent, and unsigned significand.
func (c *Context) MkFPNumeralIntUint(sgn bool, exp int, sig uint, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_numeral_int_uint(c.ptr, C.bool(sgn), C.int(exp), C.uint(sig), sort.ptr))
}

// MkFPNumeralInt64Uint64 creates a floating-point numeral from a sign, int64 exponent, and uint64 significand.
func (c *Context) MkFPNumeralInt64Uint64(sgn bool, exp int64, sig uint64, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_numeral_int64_uint64(c.ptr, C.bool(sgn), C.int64_t(exp), C.uint64_t(sig), sort.ptr))
}

// MkFPFMA creates a floating-point fused multiply-add: rm * (t1 * t2) + t3.
func (c *Context) MkFPFMA(rm, t1, t2, t3 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_fma(c.ptr, rm.ptr, t1.ptr, t2.ptr, t3.ptr))
}

// MkFPRem creates a floating-point remainder.
func (c *Context) MkFPRem(t1, t2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_rem(c.ptr, t1.ptr, t2.ptr))
}

// MkFPMin creates the minimum of two floating-point values.
func (c *Context) MkFPMin(t1, t2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_min(c.ptr, t1.ptr, t2.ptr))
}

// MkFPMax creates the maximum of two floating-point values.
func (c *Context) MkFPMax(t1, t2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_max(c.ptr, t1.ptr, t2.ptr))
}

// MkFPRoundToIntegral creates a floating-point round-to-integral operation.
func (c *Context) MkFPRoundToIntegral(rm, t *Expr) *Expr {
	return newExpr(c, C.Z3_mk_fpa_round_to_integral(c.ptr, rm.ptr, t.ptr))
}

// MkFPToFPBV converts a bit-vector to a floating-point number (reinterpretation of IEEE 754 bits).
func (c *Context) MkFPToFPBV(bv *Expr, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_fp_bv(c.ptr, bv.ptr, sort.ptr))
}

// MkFPToFPFloat converts a floating-point number to another floating-point sort with rounding.
func (c *Context) MkFPToFPFloat(rm, t *Expr, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_fp_float(c.ptr, rm.ptr, t.ptr, sort.ptr))
}

// MkFPToFPReal converts a real number to a floating-point number with rounding.
func (c *Context) MkFPToFPReal(rm, t *Expr, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_fp_real(c.ptr, rm.ptr, t.ptr, sort.ptr))
}

// MkFPToFPSigned converts a signed bit-vector to a floating-point number with rounding.
func (c *Context) MkFPToFPSigned(rm, t *Expr, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_fp_signed(c.ptr, rm.ptr, t.ptr, sort.ptr))
}

// MkFPToFPUnsigned converts an unsigned bit-vector to a floating-point number with rounding.
func (c *Context) MkFPToFPUnsigned(rm, t *Expr, sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_fp_unsigned(c.ptr, rm.ptr, t.ptr, sort.ptr))
}

// MkFPToSBV converts a floating-point number to a signed bit-vector with rounding.
func (c *Context) MkFPToSBV(rm, t *Expr, sz uint) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_sbv(c.ptr, rm.ptr, t.ptr, C.uint(sz)))
}

// MkFPToUBV converts a floating-point number to an unsigned bit-vector with rounding.
func (c *Context) MkFPToUBV(rm, t *Expr, sz uint) *Expr {
	return newExpr(c, C.Z3_mk_fpa_to_ubv(c.ptr, rm.ptr, t.ptr, C.uint(sz)))
}
