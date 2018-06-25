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
    m().inc_ref(n);
    m_mapping.insert(n, v);
    m_recent_exprs.push_back(n);
}

expr2var::expr2var(ast_manager & m):
    m_manager(m),
    m_interpreted_vars(false) {
}

expr2var::~expr2var() {
    dec_ref_map_keys(m(), m_mapping);
}

expr2var::var expr2var::to_var(expr * n) const {
    var v = UINT_MAX;
    m_mapping.find(n, v);
    return v;
}

void expr2var::display(std::ostream & out) const {
    obj_map<expr, var>::iterator it  = m_mapping.begin();
    obj_map<expr, var>::iterator end = m_mapping.end();
    for (; it != end; ++it) {
        out << mk_ismt2_pp(it->m_key, m()) << " -> " << it->m_value << "\n";
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
    dec_ref_map_keys(m(), m_mapping);
    SASSERT(m_mapping.empty());
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
            m_mapping.erase(m_recent_exprs[i]);
            m().dec_ref(m_recent_exprs[i]);
        }
        m_recent_exprs.shrink(sz);
        m_recent_lim.shrink(m_recent_lim.size() - num_scopes);
    }
}
