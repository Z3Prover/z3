/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_offset_eq.h

Abstract:

    Container for maintaining equalities between lengths of sequences.

Author:

    Thai Minh Trinh 2017
    Nikolaj Bjorner (nbjorner) 2020-4-16

--*/

#include "ast/ast_pp.h"
#include "smt/seq_offset_eq.h"
#include "smt/smt_context.h"

using namespace smt;

/**
Match:
  e  == val      where val is an integer
  e  == r1 - r2
  r1 == len(e1)
  r2 == len(e2)
update m_offset_equalities to contain.
  r1 |-> [r2 |-> val]
*/

seq_offset_eq::seq_offset_eq(theory& th, ast_manager& _m): 
    th(th), m(_m), seq(m), a(m), m_propagation_level(-1) {
    (void)m;
}

bool seq_offset_eq::match_x_minus_y(expr* e, expr*& x, expr*& y) const {
    expr* z = nullptr, *u = nullptr;
    rational fact;
    return 
        a.is_add(e, x, z) && 
        a.is_mul(z, u, y) &&
        a.is_numeral(u, fact) && 
        fact.is_minus_one();
}


void seq_offset_eq::len_offset(expr* e, int val) {
    context & ctx = th.get_context();
    expr *x = nullptr, *y = nullptr;
    expr *e1 = nullptr, *e2 = nullptr;
    if (match_x_minus_y(e, x, y) && 
        ctx.e_internalized(x) && 
        ctx.e_internalized(y)) {
        TRACE("seq", tout << "eqc: " << mk_pp(e, m) << "\n";);    
        enode* r1 = th.get_root(x);
        enode* r2 = th.get_root(y);
        for (enode* n1 : *r1) {
            if (!seq.str.is_length(n1->get_expr(), e1)) 
                continue;
            for (enode* n2 : *r2) {
                if (!seq.str.is_length(n2->get_expr(), e2)) 
                    continue;
                if (r1->get_owner_id() > r2->get_owner_id()) {
                    std::swap(r1, r2);
                    val = -val;
                }
                m_offset_equalities.insert(r1, r2, val);
                m_has_offset_equality.insert(r1);
                m_has_offset_equality.insert(r2);
                TRACE("seq", tout << "a length pair: " << mk_pp(e1, m) << ", " << mk_pp(e2, m) << "\n";);
                return;
            }
            return;
        }
    }
}

// Find the length offset from the congruence closure core
void seq_offset_eq::prop_arith_to_len_offset() {
    rational val;
    for (enode* n : th.get_context().enodes()) {
        if (a.is_numeral(n->get_expr(), val) && val.is_int32() && INT_MIN < val.get_int32()) {
            TRACE("seq", tout << "offset: " << mk_pp(n->get_expr(), m) << "\n";);
            enode *next = n->get_next();
            while (next != n) {
                len_offset(next->get_expr(), val.get_int32());
                next = next->get_next();
            }
        }
    }
}

bool seq_offset_eq::find(enode* n1, enode* n2, int& offset) const {
    n1 = n1->get_root();
    n2 = n2->get_root();
    if (n1->get_owner_id() > n2->get_owner_id()) 
        std::swap(n1, n2);
    return 
        !a.is_numeral(n1->get_expr()) && 
        !a.is_numeral(n2->get_expr()) && 
        m_offset_equalities.find(n1, n2, offset);
}

bool seq_offset_eq::contains(enode* r) {
    r = r->get_root();
    return !a.is_numeral(r->get_expr()) && m_has_offset_equality.contains(r);
}

bool seq_offset_eq::propagate() {
    context& ctx = th.get_context();
    int lvl = (int) ctx.get_scope_level();
    if (lvl > m_propagation_level) {
        m_propagation_level = lvl;
        prop_arith_to_len_offset();
        return true;
    }
    else {
        return false;
    }
}

void seq_offset_eq::pop_scope_eh(unsigned num_scopes) {
    context& ctx = th.get_context();
    int new_lvl = (int) (ctx.get_scope_level() - num_scopes);
    if (m_propagation_level > new_lvl) {
        m_propagation_level = -1;
        m_offset_equalities.reset();
        m_has_offset_equality.reset();
    }
}
