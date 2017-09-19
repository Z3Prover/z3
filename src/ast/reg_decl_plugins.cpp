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
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/dl_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/fpa_decl_plugin.h"

void reg_decl_plugins(ast_manager & m) {
    if (!m.get_plugin(m.mk_family_id(symbol("arith")))) {
        m.register_plugin(symbol("arith"), alloc(arith_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("bv")))) {
        m.register_plugin(symbol("bv"), alloc(bv_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("array")))) {
        m.register_plugin(symbol("array"), alloc(array_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("datatype")))) {
        m.register_plugin(symbol("datatype"), alloc(datatype_decl_plugin));    
    }
    if (!m.get_plugin(m.mk_family_id(symbol("datalog_relation")))) {
        m.register_plugin(symbol("datalog_relation"), alloc(datalog::dl_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("seq")))) {
        m.register_plugin(symbol("seq"), alloc(seq_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("fpa")))) {
        m.register_plugin(symbol("fpa"), alloc(fpa_decl_plugin));
    }
    if (!m.get_plugin(m.mk_family_id(symbol("pb")))) {
        m.register_plugin(symbol("pb"), alloc(pb_decl_plugin));
    }
}
