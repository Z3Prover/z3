/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "math/lp/nla_coi.h"
#include "math/lp/int_solver.h"
#include <variant>

namespace nla {

    class core;
    class lar_solver;    
    class mul_saturate : common {


        struct bound {
            lpvar v = lp::null_lpvar;
            lp::lconstraint_kind k;
            rational rhs;           
        };
        using bound_justification = std::variant<u_dependency*, bound>;

        coi m_coi;
        u_map<vector<bound_justification>> m_new_mul_constraints;
        indexed_uint_set m_to_refine;
        scoped_ptr<lp::lar_solver> lra_solver;
        scoped_ptr<lp::int_solver> int_solver;
        ptr_vector<u_dependency> m_ci2dep;
        vector<rational> m_values;
        struct eq {
            bool operator()(unsigned_vector const& a, unsigned_vector const& b) const {
                return a == b;
            }
        };
        map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
        u_map<unsigned_vector> m_mon2vars;

        // initialization
        void init_solver();
        void init_vars();
        void init_monomial(unsigned mon_var);

        bool constraint_is_true(lp::constraint_index ci);
        void insert_monomials_from_constraint(lp::constraint_index ci);

        // additional variables and monomials and constraints
        lpvar add_monomial(svector<lp::lpvar> const& vars);
        bool is_int(svector<lp::lpvar> const& vars) const;
        lpvar add_var(bool is_int);
        void add_multiply_constraints();
        void add_multiply_constraint(lp::constraint_index con_id, lp::lpvar mi, lpvar x);

        // solving
        lbool solve(lp::explanation& ex);
        lbool solve_lra(lp::explanation &ex);
        lbool solve_lia(lp::explanation &ex);

        // lemmas
        void add_lemma(lp::explanation const& ex);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, vector<std::pair<rational, lpvar>> const& lhs,
                                         lp::lconstraint_kind k, rational const& rhs) const;

    public:
        mul_saturate(core* core);
        lbool saturate();
    };

}
