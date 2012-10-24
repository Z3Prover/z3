/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_checker.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-20.

Revision History:

--*/
#include"smt_context.h"
#include"smt_checker.h"
#include"ast_ll_pp.h"

namespace smt {

    bool checker::all_args(app * a, bool is_true) {
        unsigned num_args = a->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (!check(a->get_arg(i), is_true))
                return false;
        }
        return true;
    }

    bool checker::any_arg(app * a, bool is_true) {
        unsigned num_args = a->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (check(a->get_arg(i), is_true))
                return true;
        }
        return false;
    }

    bool checker::check_core(expr * n, bool is_true) {
        SASSERT(m_manager.is_bool(n));
        if (m_context.b_internalized(n) && m_context.is_relevant(n)) {
            lbool val = m_context.get_assignment(n);
            return val != l_undef && is_true == (val == l_true);
        }
        if (!is_app(n))
            return false;
        app * a = to_app(n);
        if (a->get_family_id() == m_manager.get_basic_family_id()) {
            switch (a->get_decl_kind()) {
            case OP_TRUE:
                return is_true;
            case OP_FALSE:
                return !is_true;
            case OP_NOT:
                return check(a->get_arg(0), !is_true);
            case OP_OR:
                return is_true ? any_arg(a, true) : all_args(a, false);
            case OP_AND:
                return is_true ? all_args(a, true) : any_arg(a, false);
            case OP_IFF:
                if (is_true) {
                    return 
                        (check(a->get_arg(0), true) &&
                         check(a->get_arg(1), true)) ||
                        (check(a->get_arg(0), false) &&
                         check(a->get_arg(1), false));
                }
                else {
                    return 
                        (check(a->get_arg(0), true) &&
                         check(a->get_arg(1), false)) ||
                        (check(a->get_arg(0), false) &&
                         check(a->get_arg(1), true));
                }
            case OP_ITE: {
                if (m_context.lit_internalized(a->get_arg(0)) && m_context.is_relevant(a->get_arg(0))) {
                    switch (m_context.get_assignment(a->get_arg(0))) {
                    case l_false: return check(a->get_arg(2), is_true);
                    case l_undef: return false;
                    case l_true:  return check(a->get_arg(1), is_true);
                    }
                }
                return check(a->get_arg(1), is_true) && check(a->get_arg(2), is_true);
            }
            case OP_EQ: {
                enode * lhs = get_enode_eq_to(a->get_arg(0));
                enode * rhs = get_enode_eq_to(a->get_arg(1));
                if (lhs && rhs && m_context.is_relevant(lhs) && m_context.is_relevant(rhs)) {
                    if (is_true && lhs->get_root() == rhs->get_root())
                        return true;
                    // if (!is_true && m_context.is_ext_diseq(lhs, rhs, 2))
                    if (!is_true && m_context.is_diseq(lhs, rhs))
                        return true;
                }
                return false;
            }
            default:
                break;
            }
        }
        enode * e = get_enode_eq_to(a);
        if (e && e->is_bool() && m_context.is_relevant(e)) {
            lbool val = m_context.get_assignment(e->get_owner());
            return val != l_undef && is_true == (val == l_true);
        }
        return false;
    }
    
    bool checker::check(expr * n, bool is_true) {
        bool r;
        if (n->get_ref_count() > 1 && m_is_true_cache[is_true].find(n, r))
            return r;
        r = check_core(n, is_true);
        if (n->get_ref_count() > 1)
            m_is_true_cache[is_true].insert(n, r);
        return r;
    }

    enode * checker::get_enode_eq_to_core(app * n) {
        ptr_buffer<enode> buffer;
        unsigned num = n->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            enode * arg = get_enode_eq_to(n->get_arg(i));
            if (arg == 0) 
                return 0;
            buffer.push_back(arg);
        }
        enode * e = m_context.get_enode_eq_to(n->get_decl(), num, buffer.c_ptr());
        if (e == 0)
            return 0;
        return m_context.is_relevant(e) ? e : 0;
    }

    enode * checker::get_enode_eq_to(expr * n) {
        if (is_var(n)) { 
            unsigned idx = to_var(n)->get_idx();
            if (idx >= m_num_bindings)
                return 0;
            return m_bindings[m_num_bindings - idx - 1];
        }
        if (m_context.e_internalized(n) && m_context.is_relevant(n))
            return m_context.get_enode(n);
        if (!is_app(n) || to_app(n)->get_num_args() == 0)
            return 0;
        enode * r = 0;
        if (n->get_ref_count() > 1 && m_to_enode_cache.find(n, r)) 
            return r;
        r = get_enode_eq_to_core(to_app(n));
        if (n->get_ref_count() > 1)
            m_to_enode_cache.insert(n, r);
        return r;
    }

    bool checker::is_sat(expr * n, unsigned num_bindings, enode * const * bindings) {
        flet<unsigned>        l1(m_num_bindings, num_bindings);
        flet<enode * const *> l2(m_bindings, bindings);
        bool r = check(n, true);
        m_is_true_cache[0].reset();
        m_is_true_cache[1].reset();
        m_to_enode_cache.reset();
        return r;
    }

    bool checker::is_unsat(expr * n, unsigned num_bindings, enode * const * bindings) {
        flet<unsigned>        l1(m_num_bindings, num_bindings);
        flet<enode * const *> l2(m_bindings, bindings);
        bool r = check(n, false);
        m_is_true_cache[0].reset();
        m_is_true_cache[1].reset();
        m_to_enode_cache.reset();
        return r;
    }

    checker::checker(context & c):
        m_context(c),
        m_manager(c.get_manager()),
        m_num_bindings(0),
        m_bindings(0) {
    }
   
};



