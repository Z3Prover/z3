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
#include "math/lp/nla_grobner.h"
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
namespace nla {
nla_grobner::nla_grobner(core *c) : common(c) {}

void nla_grobner::add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, std::queue<lpvar> & q) {
    SASSERT(m_active_vars.contains(j) == false);
    const auto& matrix = c().m_lar_solver.A_r();
    m_active_vars.insert(j);
    for (auto & s : matrix.m_columns[j]) {
        unsigned row = s.var();
        if (m_rows.contains(row)) continue;
        m_rows.insert(row);
        for (auto& rc : matrix.m_rows[row]) {
            if (m_active_vars.contains(rc.var()))
                continue;
            q.push(rc.var());
        }
    }

    if (!c().is_monomial_var(j))
        return;

    const monomial& m = c().emons()[j];
    for (auto fcn : factorization_factory_imp(m, c())) {
        for (const factor& fc: fcn) {
            lpvar j = var(fc);
            if (! m_active_vars.contains(j))
                add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
        }
    }            
}

var_weight nla_grobner::get_var_weight(lpvar j) const {
    var_weight k;
    switch (c().m_lar_solver.get_column_type(j)) {
        
    case lp::column_type::fixed:
        k = var_weight::FIXED;
        break;
    case lp::column_type::boxed:
        k = var_weight::BOUNDED;
        break;
    case lp::column_type::lower_bound:
    case lp::column_type::upper_bound:
        k = var_weight::NOT_FREE;
    case lp::column_type::free_column:
        k = var_weight::FREE;
        break;
    default:
        UNREACHABLE();
        break;
    }
    if (c().is_monomial_var(j)) {
        return (var_weight)((int)k + 1);
    }
    return k;
}

void nla_grobner::set_active_vars_weights() {
    m_active_vars_weights.resize(c().m_lar_solver.column_count());
    for (lpvar j : m_active_vars) {
        m_active_vars_weights[j] = get_var_weight(j);
    }
}

void nla_grobner::find_nl_cluster() {
    prepare_rows_and_active_vars();
    std::queue<lpvar> q;
    for (lpvar j : c().m_to_refine) {        
        TRACE("nla_grobner", c().print_monomial(c().emons()[j], tout) << "\n";);
        q.push(j);
    }

    while (!q.empty()) {
        unsigned j = q.front();        
        q.pop();
        if (m_active_vars.contains(j))
            continue;
        add_var_and_its_factors_to_q_and_collect_new_rows(j, q);
    }
    set_active_vars_weights();
    TRACE("nla_grobner", display(tout););
}

void nla_grobner::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(c().m_lar_solver.row_count());
    m_active_vars.clear();
    m_active_vars.resize(c().m_lar_solver.column_count());
}

void nla_grobner::display(std::ostream & out) {
    const auto& matrix = c().m_lar_solver.A_r();
    out << "rows = " << m_rows.size() << "\n";
    for (unsigned k : m_rows) {
        c().print_term(matrix.m_rows[k], out) << "\n";
    }
    out << "the matrix =\n";
          
    for (const auto & r : matrix.m_rows) {
        c().print_term(r, out) << std::endl;
    }
}

void nla_grobner::init() {
    find_nl_cluster();
}

void nla_grobner::compute_basis(){
    compute_basis_init();        
    if (!compute_basis_loop()) {
        set_gb_exhausted();
    }
}
void nla_grobner::compute_basis_init(){
    c().lp_settings().stats().m_grobner_basis_computatins++;    
    m_num_new_equations = 0;
    
}        

bool nla_grobner::compute_basis_loop(){
    SASSERT(false);
    return false;
}

void nla_grobner::set_gb_exhausted(){ SASSERT(false); }

void nla_grobner::update_statistics(){
    SASSERT(false);
}

bool nla_grobner::find_conflict(){ SASSERT(false);
    return false;
}

bool nla_grobner::push_calculation_forward(){ SASSERT(false);
    return false;
}

void nla_grobner::grobner_lemmas() {
    c().lp_settings().stats().m_grobner_calls++;    
    init();
    do {
        TRACE("nla_gb", tout << "before:\n"; display(tout););
        compute_basis();
        update_statistics();
        TRACE("nla_gb", tout << "after:\n"; display(tout););
        if (find_conflict())
            return;
    }
    while(push_calculation_forward());
}
} // end of nla namespace
