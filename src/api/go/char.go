package z3

/*
#include "z3.h"
*/
import "C"

// Char operations

// MkCharSort creates the character sort (Unicode characters).
func (c *Context) MkCharSort() *Sort {
	return newSort(c, C.Z3_mk_char_sort(c.ptr))
}

// MkChar creates a character literal from a Unicode code point.
func (c *Context) MkChar(ch uint) *Expr {
	return newExpr(c, C.Z3_mk_char(c.ptr, C.uint(ch)))
}

// MkCharLe creates a character less-than-or-equal predicate (ch1 ≤ ch2).
func (c *Context) MkCharLe(ch1, ch2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_char_le(c.ptr, ch1.ptr, ch2.ptr))
}

// MkCharToInt converts a character to its integer (Unicode code point) value.
func (c *Context) MkCharToInt(ch *Expr) *Expr {
	return newExpr(c, C.Z3_mk_char_to_int(c.ptr, ch.ptr))
}

// MkCharToBV converts a character to a bit-vector.
func (c *Context) MkCharToBV(ch *Expr) *Expr {
	return newExpr(c, C.Z3_mk_char_to_bv(c.ptr, ch.ptr))
}

// MkCharFromBV converts a bit-vector to a character.
func (c *Context) MkCharFromBV(bv *Expr) *Expr {
	return newExpr(c, C.Z3_mk_char_from_bv(c.ptr, bv.ptr))
}

// MkCharIsDigit creates a predicate that is true if the character is a decimal digit.
func (c *Context) MkCharIsDigit(ch *Expr) *Expr {
	return newExpr(c, C.Z3_mk_char_is_digit(c.ptr, ch.ptr))
}
