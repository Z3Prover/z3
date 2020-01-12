/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  <name>

  Abstract:

  <abstract>

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  Revision History:


  --*/

#include "math/lp/horner.h"
#include "math/lp/nla_core.h"
#include "math/lp/lp_utils.h"
#include "math/lp/cross_nested.h"

namespace nla {
typedef intervals::interval interv;
horner::horner(core * c, intervals * i) : common(c, i), m_row_sum(m_nex_creator) {}

template <typename T>
bool horner::row_has_monomial_to_refine(const T& row) const {
    for (const auto& p : row) {
        if (c().m_to_refine.contains(p.var()))
            return true;
    }
    return false;
}

// Returns true if the row has at least two monomials sharing a variable
template <typename T>
bool horner::row_is_interesting(const T& row) const {
    TRACE("nla_solver_details", m_core->print_row(row, tout););
    if (row.size() > m_core->m_nla_settings.horner_row_length_limit()) {
        TRACE("nla_solver_details", tout << "disregard\n";);
        return false;
    }
    SASSERT(row_has_monomial_to_refine(row));
    c().clear_active_var_set();
    for (const auto& p : row) {
        lpvar j = p.var();
        if (!c().is_monic_var(j))
            continue;
        auto & m = c().emons()[j];
        
        for (lpvar k : m.vars()) {
            if (c().active_var_set_contains(k))
                return true;
        }
        for (lpvar k : m.vars()) {
            c().insert_to_active_var_set(k);
        }
    }
    return false;
}

bool horner::lemmas_on_expr(cross_nested& cn, nex_sum* e) {
    TRACE("nla_horner", tout << "e = " << *e << "\n";);
    cn.run(e);
    return cn.done();
}

template <typename T> 
bool horner::lemmas_on_row(const T& row) {
    SASSERT (row_is_interesting(row));
    c().clear_and_resize_active_var_set();
    u_dependency* dep = nullptr;
    create_sum_from_row(row, m_nex_creator, m_row_sum, dep);
    c().set_active_vars_weights(m_nex_creator); // without this call the comparisons will be incorrect
    nex* e =  m_nex_creator.simplify(m_row_sum.mk());
    TRACE("nla_horner", tout << "e = " << * e << "\n";);
    if (e->get_degree() < 2)
        return false;
    if (!e->is_sum())
        return false;
    
    cross_nested cn(
        [this, dep](const nex* n) { return m_intervals->check_nex(n, dep); },
        [this](unsigned j)   { return c().var_is_fixed(j); },
        [this]() { return c().random(); }, m_nex_creator);
    bool ret = lemmas_on_expr(cn, to_sum(e));
    c().m_intervals.get_dep_intervals().reset(); // clean the memory allocated by the interval bound dependencies
    return ret;

}

bool horner::horner_lemmas() {
    if (!c().m_nla_settings.run_horner()) {
        TRACE("nla_solver", tout << "not generating horner lemmas\n";);
        return false;
    }
    c().lp_settings().stats().m_horner_calls++;
    const auto& matrix = c().m_lar_solver.A_r();
    // choose only rows that depend on m_to_refine variables
    std::set<unsigned> rows_to_check;
    for (lpvar j : c().m_to_refine) {
        for (auto & s : matrix.m_columns[j])
            rows_to_check.insert(s.var());
    }
    c().clear_and_resize_active_var_set();
    svector<unsigned> rows;
    for (unsigned i : rows_to_check) {
        if (row_is_interesting(matrix.m_rows[i]))
            rows.push_back(i);
    }

    unsigned r = c().random();
    unsigned sz = rows.size();
    bool conflict = false;
    for (unsigned i = 0; i < sz && !conflict; i++) {
        m_row_index = rows[(i + r) % sz];
        if (lemmas_on_row(matrix.m_rows[m_row_index])) {
            c().lp_settings().stats().m_horner_conflicts++;
            conflict = true;
        }
    }
    return conflict;
}
}

