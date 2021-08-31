/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_axioms.cpp

Abstract:

    Axiomatize string operations that can be reduced to 
    more basic operations. These axioms are kept outside
    of a particular solver: they are mainly solver independent.

Author:

    Nikolaj Bjorner (nbjorner) 2020-4-16

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "smt/seq_axioms.h"
#include "smt/smt_context.h"

using namespace smt;

seq_axioms::seq_axioms(theory& th, th_rewriter& r):
    th(th),
    m_rewrite(r),
    m(r.m()),
    a(m),
    seq(m),
    m_sk(m, r),
    m_ax(r),
    m_digits_initialized(false)
{
    std::function<void(expr_ref_vector const&)> _add_clause = [&](expr_ref_vector const& c) { add_clause(c); };
    std::function<void(expr*)> _set_phase = [&](expr* e) { set_phase(e); };
    std::function<void(void)> _ensure_digits = [&]() { ensure_digit_axiom(); };
    m_ax.set_add_clause(_add_clause);
    m_ax.set_phase(_set_phase);
    m_ax.set_ensure_digits(_ensure_digits);
}

literal seq_axioms::mk_eq(expr* a, expr* b) {
    return th.mk_eq(a, b, false);
}

expr_ref seq_axioms::mk_sub(expr* x, expr* y) {
    expr_ref result(a.mk_sub(x, y), m);
    m_rewrite(result);
    return result;
}

expr_ref seq_axioms::mk_len(expr* s) {
    expr_ref result(seq.str.mk_length(s), m); 
    m_rewrite(result);
    return result;
}

literal seq_axioms::mk_literal(expr* _e) {
    expr_ref e(_e, m);
    if (m.is_not(_e, _e)) 
        return ~mk_literal(_e);
    if (m.is_eq(e))
        return mk_eq(to_app(e)->get_arg(0), to_app(e)->get_arg(1));
    if (a.is_arith_expr(e)) 
        m_rewrite(e);
    th.ensure_enode(e);
    return ctx().get_literal(e);
}

void seq_axioms::set_phase(expr* e) {
    literal lit = mk_literal(e);
    ctx().force_phase(lit);
}


void seq_axioms::add_clause(expr_ref_vector const& clause) {
    expr* a = nullptr, *b = nullptr;
    if (false && clause.size() == 1 && m.is_eq(clause[0], a, b)) {
        enode* n1 = th.ensure_enode(a);
        enode* n2 = th.ensure_enode(b);
        justification* js =
            ctx().mk_justification(
                ext_theory_eq_propagation_justification(
                    th.get_id(), ctx().get_region(), 0, nullptr, 0, nullptr, n1, n2));
        ctx().assign_eq(n1, n2, eq_justification(js));
        return;
    }
    literal lits[5] = { null_literal, null_literal, null_literal, null_literal, null_literal };
    unsigned idx = 0;
    for (expr* e : clause) {
        literal lit = mk_literal(e);
        if (lit == true_literal)
            return;
        if (lit != false_literal)
            lits[idx++] = mk_literal(e);
        SASSERT(idx <= 5);
    }
    add_axiom(lits[0], lits[1], lits[2], lits[3], lits[4]);
}


/**
   Bridge character digits to integers.
*/

void seq_axioms::ensure_digit_axiom() {
    if (!m_digits_initialized) {
        for (unsigned i = 0; i < 10; ++i) {
            expr_ref cnst(seq.mk_char('0'+i), m);
            add_axiom(mk_eq(m_sk.mk_digit2int(cnst), a.mk_int(i)));
        }
        ctx().push_trail(value_trail<bool>(m_digits_initialized));
        m_digits_initialized = true;
    }
}


