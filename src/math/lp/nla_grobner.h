/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

  --*/
#pragma once

#include "math/lp/nla_common.h"
#include "math/lp/nla_intervals.h"
#include "math/lp/nex.h"
#include "math/lp/cross_nested.h"
#include "math/lp/u_set.h"
#include "math/grobner/pdd_solver.h"

namespace nla {
    class core;

    class grobner : common {
        dd::pdd_manager          m_pdd_manager;
        dd::solver               m_pdd_grobner;
        lp::lar_solver&          m_lar_solver;
        lp::u_set                m_rows;

        bool propagate_bounds();
        bool propagate_eqs();
        lp::lp_settings& lp_settings();
        void find_nl_cluster();
        void prepare_rows_and_active_vars();
        void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j, svector<lpvar>& q);
        void display_matrix_of_m_rows(std::ostream& out) const;        
        void add_row(const vector<lp::row_cell<rational>>& row);
        void add_fixed_monic(unsigned j);
        bool is_solved(dd::pdd const& p, unsigned& v, dd::pdd& r);
        void add_eq(dd::pdd& p, u_dependency* dep);
        bool check_pdd_eq(const dd::solver::equation*);
        const rational& val_of_fixed_var_with_deps(lpvar j, u_dependency*& dep);
        dd::pdd pdd_expr(const rational& c, lpvar j, u_dependency*&);
        void set_level2var();
        void configure();
        std::ostream& diagnose_pdd_miss(std::ostream& out);

    public:
        grobner(core *core);        
        void operator()();
    }; 
}
