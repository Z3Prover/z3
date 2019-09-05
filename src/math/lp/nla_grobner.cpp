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
    

void nla_grobner::find_rows() {
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
    

}

void nla_grobner::prepare_rows_and_active_vars() {
    m_rows.clear();
    m_rows.resize(c().m_lar_solver.row_count());
    m_active_vars.clear();
    m_active_vars.resize(c().m_lar_solver.column_count());
}

void nla_grobner::grobner_lemmas() {
    c().lp_settings().st().m_grobner_calls++;
    if (c().lp_settings().st().m_grobner_calls == 2)
        SASSERT(false);


    find_rows();

    TRACE("nla_grobner",
          {
              const auto& matrix = c().m_lar_solver.A_r();
          tout << "rows = " << m_rows.size() << "\n";
          for (unsigned k : m_rows) {
              c().print_term(matrix.m_rows[k], tout) << "\n";
          }
          tout << "the matrix =\n";
          
          for (const auto & r : matrix.m_rows) {
              c().print_term(r, tout) << "\n";
          }
          }
          );
}
} // end of nla namespace
