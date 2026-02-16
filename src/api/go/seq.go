package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"unsafe"
)

// Sequence and string operations

// MkSeqSort creates a sequence sort.
func (c *Context) MkSeqSort(elemSort *Sort) *Sort {
	return newSort(c, C.Z3_mk_seq_sort(c.ptr, elemSort.ptr))
}

// MkStringSort creates a string sort (sequence of characters).
func (c *Context) MkStringSort() *Sort {
	return newSort(c, C.Z3_mk_string_sort(c.ptr))
}

// MkString creates a string constant.
func (c *Context) MkString(value string) *Expr {
	cStr := C.CString(value)
	defer C.free(unsafe.Pointer(cStr))
	return newExpr(c, C.Z3_mk_string(c.ptr, cStr))
}

// MkEmptySeq creates an empty sequence.
func (c *Context) MkEmptySeq(sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_seq_empty(c.ptr, sort.ptr))
}

// MkSeqUnit creates a unit sequence containing a single element.
func (c *Context) MkSeqUnit(elem *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_unit(c.ptr, elem.ptr))
}

// MkSeqConcat creates a sequence concatenation.
func (c *Context) MkSeqConcat(exprs ...*Expr) *Expr {
	if len(exprs) == 0 {
		return nil
	}
	if len(exprs) == 1 {
		return exprs[0]
	}
	cExprs := make([]C.Z3_ast, len(exprs))
	for i, e := range exprs {
		cExprs[i] = e.ptr
	}
	return newExpr(c, C.Z3_mk_seq_concat(c.ptr, C.uint(len(exprs)), &cExprs[0]))
}

// MkSeqLength creates a sequence length operation.
func (c *Context) MkSeqLength(seq *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_length(c.ptr, seq.ptr))
}

// MkSeqPrefix creates a sequence prefix predicate.
func (c *Context) MkSeqPrefix(prefix, seq *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_prefix(c.ptr, prefix.ptr, seq.ptr))
}

// MkSeqSuffix creates a sequence suffix predicate.
func (c *Context) MkSeqSuffix(suffix, seq *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_suffix(c.ptr, suffix.ptr, seq.ptr))
}

// MkSeqContains creates a sequence contains predicate.
func (c *Context) MkSeqContains(seq, substr *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_contains(c.ptr, seq.ptr, substr.ptr))
}

// MkSeqAt creates a sequence element access operation.
func (c *Context) MkSeqAt(seq, index *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_at(c.ptr, seq.ptr, index.ptr))
}

// MkSeqExtract creates a sequence extract (substring) operation.
func (c *Context) MkSeqExtract(seq, offset, length *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_extract(c.ptr, seq.ptr, offset.ptr, length.ptr))
}

// MkSeqReplace creates a sequence replace operation.
func (c *Context) MkSeqReplace(seq, src, dst *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_replace(c.ptr, seq.ptr, src.ptr, dst.ptr))
}

// MkSeqIndexOf creates a sequence index-of operation.
func (c *Context) MkSeqIndexOf(seq, substr, offset *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_index(c.ptr, seq.ptr, substr.ptr, offset.ptr))
}

// MkStrToInt creates a string-to-integer conversion.
func (c *Context) MkStrToInt(str *Expr) *Expr {
	return newExpr(c, C.Z3_mk_str_to_int(c.ptr, str.ptr))
}

// MkIntToStr creates an integer-to-string conversion.
func (c *Context) MkIntToStr(num *Expr) *Expr {
	return newExpr(c, C.Z3_mk_int_to_str(c.ptr, num.ptr))
}

// Regular expression operations

// MkReSort creates a regular expression sort.
func (c *Context) MkReSort(seqSort *Sort) *Sort {
	return newSort(c, C.Z3_mk_re_sort(c.ptr, seqSort.ptr))
}

// MkToRe converts a sequence to a regular expression that accepts exactly that sequence.
func (c *Context) MkToRe(seq *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_to_re(c.ptr, seq.ptr))
}

// MkInRe creates a membership predicate for a sequence in a regular expression.
func (c *Context) MkInRe(seq, re *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_in_re(c.ptr, seq.ptr, re.ptr))
}

// MkReStar creates a Kleene star (zero or more repetitions) of a regular expression.
func (c *Context) MkReStar(re *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_star(c.ptr, re.ptr))
}

// MkRePlus creates a Kleene plus (one or more repetitions) of a regular expression.
func (c *Context) MkRePlus(re *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_plus(c.ptr, re.ptr))
}

// MkReOption creates an optional regular expression (zero or one repetition).
func (c *Context) MkReOption(re *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_option(c.ptr, re.ptr))
}

// MkRePower creates a regular expression that matches exactly n repetitions.
func (c *Context) MkRePower(re *Expr, n uint) *Expr {
	return newExpr(c, C.Z3_mk_re_power(c.ptr, re.ptr, C.uint(n)))
}

// MkReLoop creates a regular expression with bounded repetition (between lo and hi times).
// If hi is 0, it means unbounded (at least lo times).
func (c *Context) MkReLoop(re *Expr, lo, hi uint) *Expr {
	return newExpr(c, C.Z3_mk_re_loop(c.ptr, re.ptr, C.uint(lo), C.uint(hi)))
}

// MkReConcat creates a concatenation of regular expressions.
func (c *Context) MkReConcat(regexes ...*Expr) *Expr {
	if len(regexes) == 0 {
		return nil
	}
	if len(regexes) == 1 {
		return regexes[0]
	}
	cRegexes := make([]C.Z3_ast, len(regexes))
	for i, re := range regexes {
		cRegexes[i] = re.ptr
	}
	return newExpr(c, C.Z3_mk_re_concat(c.ptr, C.uint(len(regexes)), &cRegexes[0]))
}

// MkReUnion creates a union (alternation) of regular expressions.
func (c *Context) MkReUnion(regexes ...*Expr) *Expr {
	if len(regexes) == 0 {
		return nil
	}
	if len(regexes) == 1 {
		return regexes[0]
	}
	cRegexes := make([]C.Z3_ast, len(regexes))
	for i, re := range regexes {
		cRegexes[i] = re.ptr
	}
	return newExpr(c, C.Z3_mk_re_union(c.ptr, C.uint(len(regexes)), &cRegexes[0]))
}

// MkReIntersect creates an intersection of regular expressions.
func (c *Context) MkReIntersect(regexes ...*Expr) *Expr {
	if len(regexes) == 0 {
		return nil
	}
	if len(regexes) == 1 {
		return regexes[0]
	}
	cRegexes := make([]C.Z3_ast, len(regexes))
	for i, re := range regexes {
		cRegexes[i] = re.ptr
	}
	return newExpr(c, C.Z3_mk_re_intersect(c.ptr, C.uint(len(regexes)), &cRegexes[0]))
}

// MkReComplement creates the complement of a regular expression.
func (c *Context) MkReComplement(re *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_complement(c.ptr, re.ptr))
}

// MkReDiff creates the difference of two regular expressions (a - b).
func (c *Context) MkReDiff(a, b *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_diff(c.ptr, a.ptr, b.ptr))
}

// MkReEmpty creates an empty regular expression (accepts no strings).
func (c *Context) MkReEmpty(sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_re_empty(c.ptr, sort.ptr))
}

// MkReFull creates a full regular expression (accepts all strings).
func (c *Context) MkReFull(sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_re_full(c.ptr, sort.ptr))
}

// MkReAllchar creates a regular expression that accepts all single characters.
func (c *Context) MkReAllchar(sort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_re_allchar(c.ptr, sort.ptr))
}

// MkReRange creates a regular expression for a character range [lo, hi].
func (c *Context) MkReRange(lo, hi *Expr) *Expr {
	return newExpr(c, C.Z3_mk_re_range(c.ptr, lo.ptr, hi.ptr))
}

// MkSeqReplaceRe replaces the first occurrence matching a regular expression.
func (c *Context) MkSeqReplaceRe(seq, re, replacement *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_replace_re(c.ptr, seq.ptr, re.ptr, replacement.ptr))
}

// MkSeqReplaceReAll replaces all occurrences matching a regular expression.
func (c *Context) MkSeqReplaceReAll(seq, re, replacement *Expr) *Expr {
	return newExpr(c, C.Z3_mk_seq_replace_re_all(c.ptr, seq.ptr, re.ptr, replacement.ptr))
}
