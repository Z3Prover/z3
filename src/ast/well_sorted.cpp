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
#include "ast/for_each_expr.h"
#include "ast/well_sorted.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "util/warning.h"
#include "ast/ast_smt2_pp.h"


namespace {

struct well_sorted_proc {
    ast_manager &    m;
    bool             m_error;
    ptr_vector<sort> m_binding;
    
    well_sorted_proc(ast_manager & m):m(m), m_error(false) {}

    void check(expr* e) {
        for (auto term : subterms::ground(expr_ref(e, m))) {
            if (is_app(term))
                check_app(to_app(term));
            else if (is_var(term))
                check_var(to_var(term));
            else if (is_quantifier(term))
                check_quantifier(to_quantifier(term));
        }
    }

    void check_quantifier(quantifier * n) {
        if (!is_lambda(n) && !m.is_bool(n->get_expr())) {
            warning_msg("quantifier's body must be a boolean.");
            m_error = true;
            // UNREACHABLE();
        }
        unsigned sz = m_binding.size();
        m_binding.append(n->get_num_decls(), n->get_decl_sorts());
        check(n->get_expr());
        m_binding.shrink(sz);
    }

    void check_var(var* v) {
        if (v->get_idx() >= m_binding.size()) {
            return;
        }
        sort *s = m_binding[m_binding.size() - v->get_idx() - 1];
        if (s != v->get_sort()) {
            warning_msg("variable sort does not match binding sort.");
            m_error = true;
            // UNREACHABLE();
        }
    }

    void check_app(app * n) {   
        unsigned num_args  = n->get_num_args();
        func_decl * decl   = n->get_decl();
        if (num_args != decl->get_arity() && !decl->is_associative() && 
            !decl->is_right_associative() && !decl->is_left_associative()) {
            TRACE(ws, tout << "unexpected number of arguments.\n" << mk_ismt2_pp(n, m););
            warning_msg("unexpected number of arguments.");
            m_error = true;
            return;
        }

        for (unsigned i = 0; i < num_args; ++i) {
            sort * actual_sort   = n->get_arg(i)->get_sort();
            sort * expected_sort = decl->is_associative() ? decl->get_domain(0) : decl->get_domain(i);
            if (expected_sort != actual_sort) {
                TRACE(tc, tout << "sort mismatch on argument #" << i << ".\n" << mk_ismt2_pp(n, m);
                      tout << "Sort mismatch for argument " << i+1 << " of " << mk_ismt2_pp(n, m, false) << "\n";
                      tout << "Expected sort: " << mk_pp(expected_sort, m) << "\n";
                      tout << "Actual sort:   " << mk_pp(actual_sort, m) << "\n";
                      tout << "Function sort: " << mk_pp(decl, m) << ".";
                      );
                std::ostringstream strm;
                strm << "Sort mismatch for argument " << i+1 << " of " << mk_ll_pp(n, m, false) << "\n";
                strm << "Expected sort: " << mk_pp(expected_sort, m) << '\n';
                strm << "Actual sort:   " << mk_pp(actual_sort, m) << '\n';
                strm << "Function sort: " << mk_pp(decl, m) << '.';
                warning_msg("%s", std::move(strm).str().c_str());
                m_error = true;
                // UNREACHABLE();
                return;
            }
        }
    }
};

}

bool is_well_sorted(ast_manager const & m, expr * n) {
    well_sorted_proc p(const_cast<ast_manager&>(m));
    p.check(n);
    if (p.m_error) {
        IF_VERBOSE(0, verbose_stream() << "expression is not well sorted.\n" << mk_pp(n, const_cast<ast_manager&>(m)) << "\n";);
        IF_VERBOSE(0, verbose_stream() << mk_ll_pp(n, const_cast<ast_manager &>(m)) << "\n";);
    }
    return !p.m_error;
}


