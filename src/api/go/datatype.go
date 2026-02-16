package z3

/*
#include "z3.h"
#include <stdlib.h>
*/
import "C"
import (
	"runtime"
	"unsafe"
)

// Constructor represents a datatype constructor.
type Constructor struct {
	ctx *Context
	ptr C.Z3_constructor
}

// newConstructor creates a new Constructor and manages its reference count.
func newConstructor(ctx *Context, ptr C.Z3_constructor) *Constructor {
	c := &Constructor{ctx: ctx, ptr: ptr}
	// Note: Z3_constructor doesn't use inc_ref/dec_ref pattern
	// It uses Z3_del_constructor for cleanup
	runtime.SetFinalizer(c, func(cons *Constructor) {
		C.Z3_del_constructor(cons.ctx.ptr, cons.ptr)
	})
	return c
}

// MkConstructor creates a constructor for a datatype.
// name is the constructor name, recognizer is the recognizer name,
// fieldNames are the names of the fields, and fieldSorts are the sorts of the fields.
// fieldSortRefs can be 0 for non-recursive fields or the datatype index for recursive fields.
func (c *Context) MkConstructor(name, recognizer string, fieldNames []string, fieldSorts []*Sort, fieldSortRefs []uint) *Constructor {
	cName := C.CString(name)
	cRecognizer := C.CString(recognizer)
	defer C.free(unsafe.Pointer(cName))
	defer C.free(unsafe.Pointer(cRecognizer))

	numFields := uint(len(fieldNames))
	if numFields != uint(len(fieldSorts)) || numFields != uint(len(fieldSortRefs)) {
		panic("fieldNames, fieldSorts, and fieldSortRefs must have the same length")
	}

	var cFieldNames *C.Z3_symbol
	var cSorts *C.Z3_sort
	var cSortRefs *C.uint
	
	if numFields > 0 {
		fieldSyms := make([]C.Z3_symbol, numFields)
		for i, fname := range fieldNames {
			fieldSyms[i] = c.MkStringSymbol(fname).ptr
		}
		cFieldNames = &fieldSyms[0]

		sorts := make([]C.Z3_sort, numFields)
		for i, s := range fieldSorts {
			if s != nil {
				sorts[i] = s.ptr
			}
		}
		cSorts = &sorts[0]

		refs := make([]C.uint, numFields)
		for i, r := range fieldSortRefs {
			refs[i] = C.uint(r)
		}
		cSortRefs = &refs[0]
	}

	sym := c.MkStringSymbol(name)
	recSym := c.MkStringSymbol(recognizer)
	
	return newConstructor(c, C.Z3_mk_constructor(
		c.ptr,
		sym.ptr,
		recSym.ptr,
		C.uint(numFields),
		cFieldNames,
		cSorts,
		cSortRefs,
	))
}

// ConstructorList represents a list of datatype constructors.
type ConstructorList struct {
	ctx *Context
	ptr C.Z3_constructor_list
}

// newConstructorList creates a new ConstructorList and manages its reference count.
func newConstructorList(ctx *Context, ptr C.Z3_constructor_list) *ConstructorList {
	cl := &ConstructorList{ctx: ctx, ptr: ptr}
	// Note: Z3_constructor_list doesn't use inc_ref/dec_ref pattern
	// It uses Z3_del_constructor_list for cleanup
	runtime.SetFinalizer(cl, func(list *ConstructorList) {
		C.Z3_del_constructor_list(list.ctx.ptr, list.ptr)
	})
	return cl
}

// MkConstructorList creates a list of constructors for a datatype.
func (c *Context) MkConstructorList(constructors []*Constructor) *ConstructorList {
	numCons := uint(len(constructors))
	if numCons == 0 {
		return nil
	}

	cons := make([]C.Z3_constructor, numCons)
	for i, constr := range constructors {
		cons[i] = constr.ptr
	}

	return newConstructorList(c, C.Z3_mk_constructor_list(c.ptr, C.uint(numCons), &cons[0]))
}

// MkDatatypeSort creates a datatype sort from a constructor list.
func (c *Context) MkDatatypeSort(name string, constructors []*Constructor) *Sort {
	sym := c.MkStringSymbol(name)
	
	numCons := uint(len(constructors))
	cons := make([]C.Z3_constructor, numCons)
	for i, constr := range constructors {
		cons[i] = constr.ptr
	}

	return newSort(c, C.Z3_mk_datatype(c.ptr, sym.ptr, C.uint(numCons), &cons[0]))
}

// MkDatatypeSorts creates multiple mutually recursive datatype sorts.
func (c *Context) MkDatatypeSorts(names []string, constructorLists [][]*Constructor) []*Sort {
	numTypes := uint(len(names))
	if numTypes != uint(len(constructorLists)) {
		panic("names and constructorLists must have the same length")
	}

	syms := make([]C.Z3_symbol, numTypes)
	for i, name := range names {
		syms[i] = c.MkStringSymbol(name).ptr
	}

	cLists := make([]C.Z3_constructor_list, numTypes)
	for i, constrs := range constructorLists {
		cons := make([]C.Z3_constructor, len(constrs))
		for j, constr := range constrs {
			cons[j] = constr.ptr
		}
		cLists[i] = C.Z3_mk_constructor_list(c.ptr, C.uint(len(constrs)), &cons[0])
	}

	resultSorts := make([]C.Z3_sort, numTypes)
	
	C.Z3_mk_datatypes(c.ptr, C.uint(numTypes), &syms[0], &resultSorts[0], &cLists[0])

	// Clean up constructor lists
	for i := range cLists {
		C.Z3_del_constructor_list(c.ptr, cLists[i])
	}

	sorts := make([]*Sort, numTypes)
	for i := range resultSorts {
		sorts[i] = newSort(c, resultSorts[i])
	}

	return sorts
}

// GetDatatypeSortConstructor returns the i-th constructor of a datatype sort.
func (c *Context) GetDatatypeSortConstructor(sort *Sort, i uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_get_datatype_sort_constructor(c.ptr, sort.ptr, C.uint(i)))
}

// GetDatatypeSortRecognizer returns the i-th recognizer of a datatype sort.
func (c *Context) GetDatatypeSortRecognizer(sort *Sort, i uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_get_datatype_sort_recognizer(c.ptr, sort.ptr, C.uint(i)))
}

// GetDatatypeSortConstructorAccessor returns the accessor for the i-th field of the j-th constructor.
func (c *Context) GetDatatypeSortConstructorAccessor(sort *Sort, constructorIdx, accessorIdx uint) *FuncDecl {
	return newFuncDecl(c, C.Z3_get_datatype_sort_constructor_accessor(
		c.ptr, sort.ptr, C.uint(constructorIdx), C.uint(accessorIdx)))
}

// GetDatatypeSortNumConstructors returns the number of constructors in a datatype sort.
func (c *Context) GetDatatypeSortNumConstructors(sort *Sort) uint {
	return uint(C.Z3_get_datatype_sort_num_constructors(c.ptr, sort.ptr))
}

// Tuple sorts (special case of datatypes)

// MkTupleSort creates a tuple sort with the given field sorts.
func (c *Context) MkTupleSort(name string, fieldNames []string, fieldSorts []*Sort) (*Sort, *FuncDecl, []*FuncDecl) {
	sym := c.MkStringSymbol(name)
	
	numFields := uint(len(fieldNames))
	if numFields != uint(len(fieldSorts)) {
		panic("fieldNames and fieldSorts must have the same length")
	}

	fieldSyms := make([]C.Z3_symbol, numFields)
	for i, fname := range fieldNames {
		fieldSyms[i] = c.MkStringSymbol(fname).ptr
	}

	sorts := make([]C.Z3_sort, numFields)
	for i, s := range fieldSorts {
		sorts[i] = s.ptr
	}

	var mkTupleDecl C.Z3_func_decl
	projDecls := make([]C.Z3_func_decl, numFields)

	tupleSort := C.Z3_mk_tuple_sort(
		c.ptr,
		sym.ptr,
		C.uint(numFields),
		&fieldSyms[0],
		&sorts[0],
		&mkTupleDecl,
		&projDecls[0],
	)

	projections := make([]*FuncDecl, numFields)
	for i := range projDecls {
		projections[i] = newFuncDecl(c, projDecls[i])
	}

	return newSort(c, tupleSort), newFuncDecl(c, mkTupleDecl), projections
}

// Enumeration sorts (special case of datatypes)

// MkEnumSort creates an enumeration sort with the given constants.
func (c *Context) MkEnumSort(name string, enumNames []string) (*Sort, []*FuncDecl, []*FuncDecl) {
	sym := c.MkStringSymbol(name)
	
	numEnums := uint(len(enumNames))
	enumSyms := make([]C.Z3_symbol, numEnums)
	for i, ename := range enumNames {
		enumSyms[i] = c.MkStringSymbol(ename).ptr
	}

	enumConsts := make([]C.Z3_func_decl, numEnums)
	enumTesters := make([]C.Z3_func_decl, numEnums)

	enumSort := C.Z3_mk_enumeration_sort(
		c.ptr,
		sym.ptr,
		C.uint(numEnums),
		&enumSyms[0],
		&enumConsts[0],
		&enumTesters[0],
	)

	consts := make([]*FuncDecl, numEnums)
	for i := range enumConsts {
		consts[i] = newFuncDecl(c, enumConsts[i])
	}

	testers := make([]*FuncDecl, numEnums)
	for i := range enumTesters {
		testers[i] = newFuncDecl(c, enumTesters[i])
	}

	return newSort(c, enumSort), consts, testers
}

// List sorts (special case of datatypes)

// MkListSort creates a list sort with the given element sort.
func (c *Context) MkListSort(name string, elemSort *Sort) (*Sort, *FuncDecl, *FuncDecl, *FuncDecl, *FuncDecl, *FuncDecl, *FuncDecl) {
	sym := c.MkStringSymbol(name)

	var nilDecl, consDecl, isNilDecl, isConsDecl, headDecl, tailDecl C.Z3_func_decl

	listSort := C.Z3_mk_list_sort(
		c.ptr,
		sym.ptr,
		elemSort.ptr,
		&nilDecl,
		&isNilDecl,
		&consDecl,
		&isConsDecl,
		&headDecl,
		&tailDecl,
	)

	return newSort(c, listSort),
		newFuncDecl(c, nilDecl),
		newFuncDecl(c, consDecl),
		newFuncDecl(c, isNilDecl),
		newFuncDecl(c, isConsDecl),
		newFuncDecl(c, headDecl),
		newFuncDecl(c, tailDecl)
}
