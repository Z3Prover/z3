package z3

/*
#include "z3.h"
*/
import "C"

// Regular (array-encoded) Set operations

// MkSetSort creates a set sort with the given element sort.
func (c *Context) MkSetSort(elemSort *Sort) *Sort {
	return newSort(c, C.Z3_mk_set_sort(c.ptr, elemSort.ptr))
}

// MkEmptySet creates an empty set of the given element sort.
func (c *Context) MkEmptySet(elemSort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_empty_set(c.ptr, elemSort.ptr))
}

// MkFullSet creates the full set (universe) of the given element sort.
func (c *Context) MkFullSet(elemSort *Sort) *Expr {
	return newExpr(c, C.Z3_mk_full_set(c.ptr, elemSort.ptr))
}

// MkSetAdd adds an element to a set.
func (c *Context) MkSetAdd(set, elem *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_add(c.ptr, set.ptr, elem.ptr))
}

// MkSetDel removes an element from a set.
func (c *Context) MkSetDel(set, elem *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_del(c.ptr, set.ptr, elem.ptr))
}

// MkSetUnion creates the union of two or more sets.
func (c *Context) MkSetUnion(sets ...*Expr) *Expr {
	if len(sets) == 0 {
		return nil
	}
	cSets := make([]C.Z3_ast, len(sets))
	for i, s := range sets {
		cSets[i] = s.ptr
	}
	return newExpr(c, C.Z3_mk_set_union(c.ptr, C.uint(len(sets)), &cSets[0]))
}

// MkSetIntersect creates the intersection of two or more sets.
func (c *Context) MkSetIntersect(sets ...*Expr) *Expr {
	if len(sets) == 0 {
		return nil
	}
	cSets := make([]C.Z3_ast, len(sets))
	for i, s := range sets {
		cSets[i] = s.ptr
	}
	return newExpr(c, C.Z3_mk_set_intersect(c.ptr, C.uint(len(sets)), &cSets[0]))
}

// MkSetDifference creates the set difference (set1 \ set2).
func (c *Context) MkSetDifference(set1, set2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_difference(c.ptr, set1.ptr, set2.ptr))
}

// MkSetComplement creates the complement of a set.
func (c *Context) MkSetComplement(set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_complement(c.ptr, set.ptr))
}

// MkSetMember creates a membership predicate: elem ∈ set.
func (c *Context) MkSetMember(elem, set *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_member(c.ptr, elem.ptr, set.ptr))
}

// MkSetSubset creates a subset predicate: set1 ⊆ set2.
func (c *Context) MkSetSubset(set1, set2 *Expr) *Expr {
	return newExpr(c, C.Z3_mk_set_subset(c.ptr, set1.ptr, set2.ptr))
}
