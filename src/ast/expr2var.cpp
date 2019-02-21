/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr2var.h

Abstract:

    The mapping between Z3 expressions and (low level) variables.
    Example of low level variables:
       - SAT solver
       - Polynomial 
       - etc.

Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#include "ast/expr2var.h"
#include "ast/ast_smt2_pp.h"
#include "util/ref_util.h"

void expr2var::insert(expr * n, var v) {
    if (!is_uninterp_const(n)) {
        TRACE("expr2var", tout << "interpreted:\n" << mk_ismt2_pp(n, m()) << "\n";);
        m_interpreted_vars = true;
    }
    unsigned idx = m_id2map.get(n->get_id(), UINT_MAX);
    if (idx == UINT_MAX) {
        m().inc_ref(n);
        idx = m_mapping.size();
        m_mapping.push_back(key_value(n, v));
        m_id2map.setx(n->get_id(), idx, UINT_MAX);
    }
    else {
        m_mapping[idx] = key_value(n, v);
    }

    m_recent_exprs.push_back(n);
}

expr2var::expr2var(ast_manager & m):
    m_manager(m),
    m_interpreted_vars(false) {
}

expr2var::~expr2var() {
    for (auto & kv : m_mapping) {
        m().dec_ref(kv.m_key);
    }
}

expr2var::var expr2var::to_var(expr * n) const {
    var v = m_id2map.get(n->get_id(), UINT_MAX);
    if (v != UINT_MAX) {
        v = m_mapping[v].m_value;
    }
    return v;
}

void expr2var::display(std::ostream & out) const {
    for (auto const& kv : m_mapping) {
        out << mk_ismt2_pp(kv.m_key, m()) << " -> " << kv.m_value << "\n";
    }
}

void expr2var::mk_inv(expr_ref_vector & var2expr) const {
    for (auto & kv : m_mapping) {
        expr * t = kv.m_key;
        var x = kv.m_value;
        if (x >= var2expr.size())
            var2expr.resize(x+1, nullptr);
        var2expr.set(x, t);
    }
}

void expr2var::reset() {
    for (auto & kv : m_mapping) {
        m().dec_ref(kv.m_key);
    }
    m_mapping.reset();
    m_id2map.reset();
    m_recent_exprs.reset();
    m_recent_lim.reset();
    m_interpreted_vars = false;
}

void expr2var::push() {
    m_recent_lim.push_back(m_recent_exprs.size());
}

void expr2var::pop(unsigned num_scopes) {
    if (num_scopes > 0) {
        unsigned sz = m_recent_lim[m_recent_lim.size() - num_scopes];
        for (unsigned i = sz; i < m_recent_exprs.size(); ++i) {
            expr* n = m_recent_exprs[i];
            unsigned idx = m_id2map[n->get_id()];
            if (idx + 1 != m_mapping.size()) {
                m_id2map[m_mapping.back().m_key->get_id()] = idx;
                m_mapping[idx] = m_mapping.back();
            }
            m_id2map[n->get_id()] = UINT_MAX;
            m_mapping.pop_back();
            m().dec_ref(n);
        }
        m_recent_exprs.shrink(sz);
        m_recent_lim.shrink(m_recent_lim.size() - num_scopes);
    }
}
