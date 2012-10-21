/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    arith_solver_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-30.

Revision History:

--*/
#include"arith_solver_plugin.h"
#include"ast_pp.h"

arith_solver_plugin::arith_solver_plugin(arith_simplifier_plugin & simp):
    solver_plugin(symbol("arith"), simp.get_manager()),
    m_simplifier(simp) {
}

bool arith_solver_plugin::solve(expr * lhs, expr * rhs, expr_mark const & forbidden, app_ref & var, expr_ref & subst) {
    rational k;
    if (!m_simplifier.is_numeral(rhs, k))
        return false;
    bool _is_int = m_simplifier.is_int(lhs);
    ptr_buffer<expr> monomials;
    ptr_buffer<expr> todo;
    bool already_found = false;
    rational c;
    todo.push_back(lhs);
    while (!todo.empty()) {
        expr * curr = todo.back();
        todo.pop_back();
        rational coeff;
        if (m_simplifier.is_add(curr)) {
            SASSERT(to_app(curr)->get_num_args() == 2);
            todo.push_back(to_app(curr)->get_arg(1));
            todo.push_back(to_app(curr)->get_arg(0));
        }
        else {
            if (!already_found) {
                if (m_simplifier.is_mul(curr) && 
                    m_simplifier.is_numeral(to_app(curr)->get_arg(0), coeff) && !coeff.is_zero() && (!_is_int || coeff.is_minus_one()) && 
                    is_uninterp_const(to_app(curr)->get_arg(1)) &&
                    !forbidden.is_marked(to_app(curr)->get_arg(1))) {
                    c             = coeff;
                    var           = to_app(to_app(curr)->get_arg(1));
                    already_found = true;
                }
                else if (is_uninterp_const(curr) && !forbidden.is_marked(curr)) {
                    c             = rational::one();
                    var           = to_app(curr);
                    already_found = true;
                }
                else {
                    monomials.push_back(curr);
                }
            }
            else {
                monomials.push_back(curr);
            }
        }
    }
    if (!already_found)
        return false;
    SASSERT(!c.is_zero());
    k /= c;
    expr_ref_vector new_monomials(m_manager);
    if (!k.is_zero())
        new_monomials.push_back(m_simplifier.mk_numeral(k, _is_int));
    c.neg();
    expr_ref inv_c(m_manager);
    if (!c.is_one()) {
        rational inv(1);
        inv /= c;
        inv_c = m_simplifier.mk_numeral(inv, _is_int);
    }
    // divide monomials by c
    unsigned sz = monomials.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * m       = monomials[i];
        expr_ref new_m(m_manager); 
        if (!c.is_one())
            m_simplifier.mk_mul(inv_c, m, new_m);
        else
            new_m = m;
        new_monomials.push_back(new_m);
    }
    if (new_monomials.empty()) 
        subst = m_simplifier.mk_numeral(rational(0), _is_int);
    else
        m_simplifier.mk_add(new_monomials.size(), new_monomials.c_ptr(), subst);
    TRACE("arith_solver", tout << "solving:\n" << mk_pp(lhs, m_manager) << "\n" << mk_pp(rhs, m_manager) 
          << "\nresult:\n" << mk_pp(var, m_manager) << "\n" << mk_pp(subst, m_manager) << "\n";);
    return true;
}


