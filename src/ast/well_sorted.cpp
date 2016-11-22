/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    well_sorted.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-29.

Revision History:

--*/

#include<sstream>
#include"for_each_expr.h"
#include"well_sorted.h"
#include"ast_ll_pp.h"
#include"ast_pp.h"
#include"warning.h"
#include"ast_smt2_pp.h"

struct well_sorted_proc {
    ast_manager & m_manager;
    bool          m_error;
    
    well_sorted_proc(ast_manager & m):m_manager(m), m_error(false) {}
    
    void operator()(var * v) {}

    void operator()(quantifier * n) {
        expr const * e  = n->get_expr();
        if (!m_manager.is_bool(e)) {
            warning_msg("quantifier's body must be a boolean.");
            m_error = true;
        }
    }

    void operator()(app * n) {   
        unsigned num_args  = n->get_num_args();
        func_decl * decl   = n->get_decl();
        if (num_args != decl->get_arity() && !decl->is_associative() && 
            !decl->is_right_associative() && !decl->is_left_associative()) {
            TRACE("ws", tout << "unexpected number of arguments.\n" << mk_ismt2_pp(n, m_manager););
            warning_msg("unexpected number of arguments.");
            m_error = true;
            return;
        }

        for (unsigned i = 0; i < num_args; i++) {
            sort * actual_sort   = m_manager.get_sort(n->get_arg(i));
            sort * expected_sort = decl->is_associative() ? decl->get_domain(0) : decl->get_domain(i);
            if (expected_sort != actual_sort) {
                TRACE("tc", tout << "sort mismatch on argument #" << i << ".\n" << mk_ismt2_pp(n, m_manager);
                      tout << "Sort mismatch for argument " << i+1 << " of " << mk_ismt2_pp(n, m_manager, false) << "\n";
                      tout << "Expected sort: " << mk_pp(expected_sort, m_manager) << "\n";
                      tout << "Actual sort:   " << mk_pp(actual_sort, m_manager) << "\n";
                      tout << "Function sort: " << mk_pp(decl, m_manager) << ".";
                      );
                std::ostringstream strm;
                strm << "Sort mismatch for argument " << i+1 << " of " << mk_ll_pp(n, m_manager, false) << "\n";
                strm << "Expected sort: " << mk_pp(expected_sort, m_manager) << "\n";
                strm << "Actual sort:   " << mk_pp(actual_sort, m_manager) << "\n";
                strm << "Function sort: " << mk_pp(decl, m_manager) << ".";
                warning_msg("%s", strm.str().c_str());
                m_error = true;
                return;
            }
        }
    }
};

bool is_well_sorted(ast_manager const & m, expr * n) {
    well_sorted_proc p(const_cast<ast_manager&>(m));
    for_each_expr(p, n);
    return !p.m_error;
}


