/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_v1.h

Abstract:

    Z3 1.x backwards compatibility macros.
    These macros are used to simulate the Z3 API using in the 1.x versions.
    This file should only be used by users still using the Z3 1.x API.

Author:

    Leonardo de Moura (leonardo) 2011-09-22

Notes:
    
--*/
#ifndef _Z3_V1_H_
#define _Z3_V1_H_

#include"z3.h"

// Backwards compatibility
#define Z3_type_ast            Z3_sort
#define Z3_const_decl_ast      Z3_func_decl
#define Z3_const               Z3_app
#define Z3_pattern_ast         Z3_pattern
#define Z3_UNINTERPRETED_TYPE  Z3_UNINTERPRETED_SORT
#define Z3_BOOL_TYPE           Z3_BOOL_SORT
#define Z3_INT_TYPE            Z3_INT_SORT
#define Z3_REAL_TYPE           Z3_REAL_SORT
#define Z3_BV_TYPE             Z3_BV_SORT
#define Z3_ARRAY_TYPE          Z3_ARRAY_SORT
#define Z3_TUPLE_TYPE          Z3_DATATYPE_SORT
#define Z3_UNKNOWN_TYPE        Z3_UNKNOWN_SORT
#define Z3_CONST_DECL_AST      Z3_FUNC_DECL_AST    
#define Z3_TYPE_AST            Z3_SORT_AST          
#define Z3_SORT_ERROR          Z3_TYPE_ERROR
#define Z3_mk_uninterpreted_type Z3_mk_uninterpreted_sort
#define Z3_mk_bool_type        Z3_mk_bool_sort
#define Z3_mk_int_type         Z3_mk_int_sort
#define Z3_mk_real_type        Z3_mk_real_sort
#define Z3_mk_bv_type          Z3_mk_bv_sort
#define Z3_mk_array_type       Z3_mk_array_sort
#define Z3_mk_tuple_type       Z3_mk_tuple_sort
#define Z3_get_type            Z3_get_sort
#define Z3_get_pattern_ast           Z3_get_pattern
#define Z3_get_type_kind             Z3_get_sort_kind
#define Z3_get_type_name             Z3_get_sort_name
#define Z3_get_bv_type_size          Z3_get_bv_sort_size
#define Z3_get_array_type_domain     Z3_get_array_sort_domain
#define Z3_get_array_type_range      Z3_get_array_sort_range
#define Z3_get_tuple_type_num_fields Z3_get_tuple_sort_num_fields
#define Z3_get_tuple_type_field_decl Z3_get_tuple_sort_field_decl
#define Z3_get_tuple_type_mk_decl    Z3_get_tuple_sort_mk_decl
#define Z3_to_const_ast              Z3_to_app
#define Z3_get_numeral_value_string  Z3_get_numeral_string
#define Z3_get_const_ast_decl        Z3_get_app_decl
#define Z3_get_value                 Z3_eval_func_decl

#endif
