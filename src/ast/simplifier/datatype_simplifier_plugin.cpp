/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    datatype_simplifier_plugin.cpp

Abstract:

    Simplifier for algebraic datatypes.

Author:

    nbjorner 2008-11-6
    
--*/

#include"datatype_simplifier_plugin.h"

datatype_simplifier_plugin::datatype_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b):
    simplifier_plugin(symbol("datatype"), m),
    m_util(m),
    m_bsimp(b) {
}

datatype_simplifier_plugin::~datatype_simplifier_plugin() {
}

bool datatype_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();

    SASSERT(f->get_family_id() == get_family_id());
    switch(f->get_decl_kind()) {
    case OP_DT_CONSTRUCTOR: {
        return false;
    }
    case OP_DT_RECOGNISER: {
        //
        // simplify is_cons(cons(x,y)) -> true
        // simplify is_cons(nil) -> false
        //
        SASSERT(num_args == 1);
        
        if (!is_app_of(args[0], get_family_id(), OP_DT_CONSTRUCTOR)) {
            return false;
        }
        app* a = to_app(args[0]);
        func_decl* f1 = a->get_decl();
        func_decl* f2 = m_util.get_recognizer_constructor(f);
        if (f1 == f2) {
            result = m_manager.mk_true();
        }
        else {
            result = m_manager.mk_false();
        }
        return true;
    }
    case OP_DT_ACCESSOR: {
        // 
        // simplify head(cons(x,y)) -> x
        // 
        SASSERT(num_args == 1);
        
        if (!is_app_of(args[0], get_family_id(), OP_DT_CONSTRUCTOR)) {
            return false;
        }
        app* a = to_app(args[0]);
        func_decl* f1 = a->get_decl();
        func_decl* f2 = m_util.get_accessor_constructor(f);
        if (f1 != f2) {
            return false;
        }
        ptr_vector<func_decl> const* acc = m_util.get_constructor_accessors(f1);
        SASSERT(acc && acc->size() == a->get_num_args());
        for (unsigned i = 0; i < acc->size(); ++i) {
            if (f == (*acc)[i]) {
                // found it.
                result = a->get_arg(i);
                return true;
            }
        }
        UNREACHABLE();
    }
    case OP_DT_UPDATE_FIELD:
        return false;
    default:
        UNREACHABLE();
    }
    
    return false;
}

bool datatype_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    set_reduce_invoked();
    if (is_app_of(lhs, get_family_id(), OP_DT_CONSTRUCTOR) &&
        is_app_of(rhs, get_family_id(), OP_DT_CONSTRUCTOR)) {
        app* a = to_app(lhs);
        app* b = to_app(rhs);
        if (a->get_decl() != b->get_decl()) {
            result = m_manager.mk_false();
            return true;
        }
        expr_ref_vector eqs(m_manager);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {            
            m_bsimp.mk_eq(a->get_arg(i),b->get_arg(i), result);
            eqs.push_back(result);                
        }
        m_bsimp.mk_and(eqs.size(), eqs.c_ptr(), result);
        return true;
    }
    // TBD: occurs check, constructor check.

    return false;
}

