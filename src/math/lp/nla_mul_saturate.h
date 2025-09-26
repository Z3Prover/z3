/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

namespace nla {

    class core;
    class lar_solver;
    class mul_saturate : common {
        // source of multiplication constraint
        u_map<lp::constraint_index> m_new_mul_constraints;
        svector<std::pair<lpvar, bool>> m_var_signs;
        tracked_uint_set m_seen_vars;
        scoped_ptr<lp::lar_solver> local_solver;
        void init_solver();
        void add_multiply_constraints();
        void add_multiply_constraint(lp::constraint_index con_id, lp::lpvar mi, lpvar x);
        lbool solve(lp::explanation& ex);
        void add_lemma(lp::explanation const& ex1);
    public:
        mul_saturate(core* core);

        lbool saturate();
    };

}
