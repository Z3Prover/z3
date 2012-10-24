/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reg_decl_plugins

Abstract:

    Goodie for installing all available declarations
    plugins in an ast_manager

Author:

    Leonardo de Moura (leonardo) 2012-10-24.

Revision History:

--*/
#include"ast.h"
#include"arith_decl_plugin.h"
#include"array_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"seq_decl_plugin.h"
#include"float_decl_plugin.h"

void reg_decl_plugins(ast_manager & m) {
    if (!get_plugin(get_family_id(symbol("arith")))) {
        register_plugin(symbol("arith"), alloc(arith_decl_plugin));
    }
    if (!get_plugin(get_family_id(symbol("bv")))) {
        register_plugin(symbol("bv"), alloc(bv_decl_plugin));
    }
    if (!get_plugin(get_family_id(symbol("array")))) {
        register_plugin(symbol("array"), alloc(array_decl_plugin));
    }
    if (!get_plugin(get_family_id(symbol("datatype")))) {
        register_plugin(symbol("datatype"), alloc(datatype_decl_plugin));    
    }
    if (!get_plugin(get_family_id(symbol("datalog_relation")))) {
        register_plugin(symbol("datalog_relation"), alloc(datalog::dl_decl_plugin));
    }
    if (!get_plugin(get_family_id(symbol("seq")))) {
        register_plugin(symbol("seq"), alloc(seq_decl_plugin));
    }
    if (!get_plugin(get_family_id(symbol("float")))) {
        register_plugin(symbol("float"), alloc(float_decl_plugin));
    }
}
