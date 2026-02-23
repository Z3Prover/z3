package z3

/*
#include "z3.h"
*/
import "C"

// Finite set operations

// MkFiniteSetSort creates a finite set sort with the given element sort.
func (c *Context) MkFiniteSetSort(elemSort *Sort) *Sort {
	return newSort(c, C.Z3_mk_finite_set_sort(c.ptr, elemSort.ptr))
}

// IsFiniteSetSort returns true if the given sort is a finite set sort.
func (c *Context) IsFiniteSetSort(s *Sort) bool {
	return bool(C.Z3_is_finite_set_sort(c.ptr, s.ptr))
}

// GetFiniteSetSortBasis returns the element sort of a finite set sort.
func (c *Context) GetFiniteSetSortBasis(s *Sort) *Sort {
	return newSort(c, C.Z3_get_finite_set_sort_basis(c.ptr, s.ptr))
}

// MkFiniteSetEmpty creates an empty finite set of the given sort.
func (c *Context) MkFiniteSetEmpty(setSort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_empty(c.ptr, setSort.ptr))
}

// MkFiniteSetSingleton creates a singleton finite set containing the given element.
func (c *Context) MkFiniteSetSingleton(elem *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_singleton(c.ptr, elem.ptr))
}

// MkFiniteSetUnion creates the union of two finite sets.
func (c *Context) MkFiniteSetUnion(s1, s2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_union(c.ptr, s1.ptr, s2.ptr))
}

// MkFiniteSetIntersect creates the intersection of two finite sets.
func (c *Context) MkFiniteSetIntersect(s1, s2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_intersect(c.ptr, s1.ptr, s2.ptr))
}

// MkFiniteSetDifference creates the set difference of two finite sets (s1 \ s2).
func (c *Context) MkFiniteSetDifference(s1, s2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_difference(c.ptr, s1.ptr, s2.ptr))
}

// MkFiniteSetMember creates a membership predicate: elem ∈ set.
func (c *Context) MkFiniteSetMember(elem, set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_member(c.ptr, elem.ptr, set.ptr))
}

// MkFiniteSetSize creates an expression for the cardinality of a finite set.
func (c *Context) MkFiniteSetSize(set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_size(c.ptr, set.ptr))
}

// MkFiniteSetSubset creates a subset predicate: s1 ⊆ s2.
func (c *Context) MkFiniteSetSubset(s1, s2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_subset(c.ptr, s1.ptr, s2.ptr))
}

// MkFiniteSetMap applies a function to all elements of a finite set.
func (c *Context) MkFiniteSetMap(f, set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_map(c.ptr, f.ptr, set.ptr))
}

// MkFiniteSetFilter filters a finite set using a predicate function.
func (c *Context) MkFiniteSetFilter(f, set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_filter(c.ptr, f.ptr, set.ptr))
}

// MkFiniteSetRange creates a finite set of integers in the range [low, high].
func (c *Context) MkFiniteSetRange(low, high *Expr) *Expr {
	return newExpr(c, C.Z3_mk_finite_set_range(c.ptr, low.ptr, high.ptr))
}
