/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_simplifier_plugin.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-08-10

Revision History:

--*/

#include"dl_simplifier_plugin.h"

namespace datalog {

    dl_simplifier_plugin::dl_simplifier_plugin(ast_manager& m) 
        : simplifier_plugin(symbol("datalog_relation"), m),
          m_util(m)
    {}
        
    bool dl_simplifier_plugin::reduce(
        func_decl * f, unsigned num_args, expr* const* args, expr_ref& result) {
        uint64 v1, v2;
        switch(f->get_decl_kind()) {
        case OP_DL_LT:
            if (m_util.try_get_constant(args[0], v1) &&
                m_util.try_get_constant(args[1], v2)) {
                result = (v1 < v2)?m_manager.mk_true():m_manager.mk_false();
                return true;
            }
            // x < x <=> false
            if (args[0] == args[1]) {
                result = m_manager.mk_false();
                return true;
            }
            // x < 0 <=> false
            if (m_util.try_get_constant(args[1], v2) && v2 == 0) {
                result = m_manager.mk_false();
                return true;
            }
            // 0 < x <=> 0 != x
            if (m_util.try_get_constant(args[1], v1) && v1 == 0) {
                result = m_manager.mk_not(m_manager.mk_eq(args[0], args[1]));
                return true;
            }
            break;

        default:
            break;
        }
        return false;
    }
    
};


