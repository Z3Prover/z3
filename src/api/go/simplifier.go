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

// Simplifier represents a Z3 simplifier for pre-processing solver assertions.
type Simplifier struct {
	ctx *Context
	ptr C.Z3_simplifier
}

// newSimplifier creates a new Simplifier and manages its reference count.
func newSimplifier(ctx *Context, ptr C.Z3_simplifier) *Simplifier {
	s := &Simplifier{ctx: ctx, ptr: ptr}
	C.Z3_simplifier_inc_ref(ctx.ptr, ptr)
	runtime.SetFinalizer(s, func(simp *Simplifier) {
		C.Z3_simplifier_dec_ref(simp.ctx.ptr, simp.ptr)
	})
	return s
}

// MkSimplifier creates a simplifier with the given name.
func (c *Context) MkSimplifier(name string) *Simplifier {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))
	return newSimplifier(c, C.Z3_mk_simplifier(c.ptr, cName))
}

// AndThen creates a simplifier that applies s followed by s2.
func (s *Simplifier) AndThen(s2 *Simplifier) *Simplifier {
	return newSimplifier(s.ctx, C.Z3_simplifier_and_then(s.ctx.ptr, s.ptr, s2.ptr))
}

// UsingParams creates a simplifier that uses the given parameters.
func (s *Simplifier) UsingParams(params *Params) *Simplifier {
	return newSimplifier(s.ctx, C.Z3_simplifier_using_params(s.ctx.ptr, s.ptr, params.ptr))
}

// GetHelp returns help information for the simplifier.
func (s *Simplifier) GetHelp() string {
	return C.GoString(C.Z3_simplifier_get_help(s.ctx.ptr, s.ptr))
}

// GetParamDescrs returns parameter descriptions for the simplifier.
func (s *Simplifier) GetParamDescrs() *ParamDescrs {
	return newParamDescrs(s.ctx, C.Z3_simplifier_get_param_descrs(s.ctx.ptr, s.ptr))
}

// GetSimplifierDescr returns a description of the simplifier with the given name.
func (c *Context) GetSimplifierDescr(name string) string {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))
	return C.GoString(C.Z3_simplifier_get_descr(c.ptr, cName))
}
