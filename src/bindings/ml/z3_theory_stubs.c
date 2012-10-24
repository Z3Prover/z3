/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    z3_theory_stubs.c

Abstract:

    OCaml C bindings for callbacks between OCaml and C for
    theory plugins. 
    The API for theory plugins require associating a set of
    callbacks as C function pointers.  
    We use the following strategy:

    - store in the user_ext_data blob that theory constructors allow
      a record of callback functions.

    - define catch-all static callback functions that access the 
      ML record with the callbacks. It then invokes these through user-registered
      application functions that apply the callback stored in the record to the
      actual parameters.
      It is tempting to avoid this user-registered callback and directly access 
      the record of callback functions and apply the proper field. 
      However, the layout of records appears to be opaque, or at least we assume it is
      so, from the C runtime.

Author:


Revision History:
--*/

#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif

#include "z3.h"

#define ML_SIZE(_ty) ((sizeof(_ty) + sizeof(value) - 1)/ sizeof(value))

static value mk_func_decl(Z3_func_decl f) {
    value _f = alloc(ML_SIZE(Z3_func_decl), Abstract_tag);
    *((Z3_func_decl*) Bp_val(_f)) = f;
    return _f;
}

static value Val_ast(Z3_ast a) {
    value _a = alloc(ML_SIZE(Z3_ast), Abstract_tag);
    *((Z3_ast*) Bp_val(_a)) = a;
    return _a;
}


static value Val_ast_array(unsigned int sz, Z3_ast const args[]) {
    value res;
    Z3_ast* args1;
    unsigned int i;
    args1 = malloc((sz+1)*sizeof(Z3_ast));
    for (i = 0; i < sz; ++i) {
        args1[i] = args[i];
    }
    args1[sz] = 0;
    res = alloc_array((value (*)(char const*))Val_ast, (const char**)args1);
    free(args1);
    return res;
}

// ------------------
// get_theory_callbacks
// 

value get_theory_callbacks(value th) 
{
    Z3_theory _th = *((Z3_theory*) Bp_val(th));
    return (value) Z3_theory_get_ext_data(_th);
}

// ------------------
// delete_theory
// 
static void delete_callback_static(Z3_theory th) 
{
    CAMLparam0();
    CAMLlocal1(f);  
    value user_data = (value) Z3_theory_get_ext_data(th);
    f = *(caml_named_value("apply_delete")) ;
    callback(f, user_data);
    remove_global_root(&user_data);
    CAMLreturn0;
}

#define SET_CALLBACK(_cb_name)                     \
    value set_ ## _cb_name ## _callback_register(value th)  \
    {                                              \
        CAMLparam1(th);                                         \
        Z3_theory _th = *((Z3_theory*) Bp_val(th));                     \
        Z3_set_ ## _cb_name ## _callback(_th, _cb_name ## _callback_static);   \
        CAMLreturn(Val_unit);                                           \
    }                                                                   \

SET_CALLBACK(delete);


// ------------------
// mk_theory
// 

value mk_theory_register(value context, value name, value user_data) 
{
    CAMLparam3(context, name, user_data);
    Z3_context _context = *((Z3_context *) Bp_val(context));
    value _th;
    Z3_theory th;
    register_global_root(&user_data);
    th = Z3_mk_theory(_context, String_val(name), (void*)user_data);
    // jjb: test th == NULL ?
    Z3_set_delete_callback(th, delete_callback_static);
    _th = alloc(ML_SIZE(Z3_context), Abstract_tag);
    *((Z3_theory*) Bp_val(_th)) = th;
    CAMLreturn(_th);
}


// -------------------
// reduce_app_callback

static Z3_bool reduce_app_callback_static(Z3_theory th, Z3_func_decl f, unsigned num_args, Z3_ast const args[], Z3_ast* r) {
    CAMLparam0();
    CAMLlocal4(cb, _r, _v, _args);
    value user_data;
    Z3_bool result;

    _args = Val_ast_array(num_args, args);

    user_data = (value) Z3_theory_get_ext_data(th);

    cb = *(caml_named_value("apply_reduce_app"));
    _r = callback3(cb, user_data, mk_func_decl(f), _args);

    cb = *(caml_named_value("is_some"));
    _v = callback(cb, _r);
    result = 0 != Bool_val(_v);

    if (result && r) {
        cb = *(caml_named_value("get_some"));
        _v = callback(cb, _r);
        *r = *((Z3_ast*) Bp_val(_v));
    }

    CAMLreturn (result);
}

SET_CALLBACK(reduce_app);

// -------------------
// reduce_eq_callback

static Z3_bool reduce_eq_callback_static(Z3_theory th, Z3_ast a, Z3_ast b, Z3_ast * r) 
{
    CAMLparam0();
    CAMLlocal5(cb, _r, _a, _b, _v);
    value user_data;
    Z3_bool result;

    _a = Val_ast(a);
    _b = Val_ast(b);

    user_data = (value) Z3_theory_get_ext_data(th);

    cb = *(caml_named_value("apply_reduce_eq"));
    _r = callback3(cb, user_data, _a, _b);

    cb = *(caml_named_value("is_some"));
    _v = callback(cb, _r);
    result = 0 != Bool_val(_v);

    if (result && r) {
        cb = *(caml_named_value("get_some"));
        _v = callback(cb, _r);
        *r = *((Z3_ast*) Bp_val(_v));
    }

    CAMLreturn (result);
}

SET_CALLBACK(reduce_eq);


// -------------------
// reduce_distinct

static Z3_bool reduce_distinct_callback_static(Z3_theory th, unsigned n, Z3_ast const args[], Z3_ast * r)
{
    CAMLparam0();
    CAMLlocal4(cb, _r, _args, _v);
    value user_data;
    Z3_bool result;

    _args = Val_ast_array(n, args);

    user_data = (value) Z3_theory_get_ext_data(th);

    cb = *(caml_named_value("apply_reduce_distinct"));
    _r = callback2(cb, user_data, _args);

    cb = *(caml_named_value("is_some"));
    _v = callback(cb, _r);
    result = 0 != Bool_val(_v);

    if (result && r) {
        cb = *(caml_named_value("get_some"));
        _v = callback(cb, _r);
        *r = *((Z3_ast*) Bp_val(_v));
    }

    CAMLreturn (result);
}

SET_CALLBACK(reduce_distinct);

// -------------------
// new_app

#define AST_CALLBACK(_cb_name) \
static void _cb_name##_callback_static(Z3_theory th, Z3_ast a)        \
{                                                           \
    CAMLparam0();                                           \
    CAMLlocal3(cb, _a, user_data);                          \
    _a = Val_ast(a);                                         \
    user_data = (value) Z3_theory_get_ext_data(th);         \
    cb = *(caml_named_value("apply_" #_cb_name));           \
    callback2(cb, user_data, _a);                           \
    CAMLreturn0;                                            \
}                                                           \

AST_CALLBACK(new_app);
SET_CALLBACK(new_app);

// -------------------
// new_elem

AST_CALLBACK(new_elem);
SET_CALLBACK(new_elem);

// -------------------
// init_search

#define TH_CALLBACK(_cb_name) \
static void _cb_name##_callback_static(Z3_theory th)        \
{                                                           \
    CAMLparam0();                                           \
    CAMLlocal2(cb, user_data);                              \
    user_data = (value) Z3_theory_get_ext_data(th);         \
    cb = *(caml_named_value("apply_" #_cb_name));           \
    callback(cb, user_data);                                \
    CAMLreturn0;                                            \
}                                                           \

TH_CALLBACK(init_search);
SET_CALLBACK(init_search);

// -------------------
// push

TH_CALLBACK(push);
SET_CALLBACK(push);

TH_CALLBACK(pop);
SET_CALLBACK(pop);

TH_CALLBACK(restart);
SET_CALLBACK(restart);

TH_CALLBACK(reset);
SET_CALLBACK(reset);

        
#define FC_CALLBACK(_cb_name) \
    static Z3_bool _cb_name##_callback_static(Z3_theory th)             \
    {                                                                   \
    CAMLparam0();                                                       \
    CAMLlocal3(cb, r, user_data);                                       \
    user_data = (value) Z3_theory_get_ext_data(th);                     \
    cb = *(caml_named_value("apply_" #_cb_name));                       \
    r = callback(cb, user_data);                                        \
    CAMLreturn (Bool_val(r) != 0);                                      \
    }                                                                   \
    
FC_CALLBACK(final_check);
SET_CALLBACK(final_check);

#define AST_AST_CALLBACK(_cb_name) \
    static void _cb_name##_callback_static(Z3_theory th, Z3_ast a, Z3_ast b)     \
    {                                                                   \
        CAMLparam0();                                                   \
        CAMLlocal4(cb, _a, _b, user_data);                              \
        _a = Val_ast(a);                                                \
        _b = Val_ast(b);                                                \
        user_data = (value) Z3_theory_get_ext_data(th);                 \
        cb = *(caml_named_value("apply_" #_cb_name));                   \
        callback3(cb, user_data, _a, _b);                               \
        CAMLreturn0;                                                    \
    }                                                                   \
    
AST_AST_CALLBACK(new_eq);
SET_CALLBACK(new_eq);

AST_AST_CALLBACK(new_diseq);
SET_CALLBACK(new_diseq);

#define AST_BOOL_CALLBACK(_cb_name) \
    static void _cb_name##_callback_static(Z3_theory th, Z3_ast a, Z3_bool b)     \
    {                                                                   \
        CAMLparam0();                                                   \
        CAMLlocal4(cb, _a, _b, user_data);                              \
        _a = Val_ast(a);                                                \
        _b = Val_bool(b);                                               \
        user_data = (value) Z3_theory_get_ext_data(th);                 \
        cb = *(caml_named_value("apply_" #_cb_name));                   \
        callback3(cb, user_data, _a, _b);                               \
        CAMLreturn0;                                                    \
    }                                                                   \

    
AST_BOOL_CALLBACK(new_assignment);
SET_CALLBACK(new_assignment);

AST_CALLBACK(new_relevant);
SET_CALLBACK(new_relevant);

