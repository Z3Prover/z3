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
    class stellensatz : common {

        class solver {            
            stellensatz &s;
            scoped_ptr<lp::lar_solver> lra_solver;
            scoped_ptr<lp::int_solver> int_solver;
            lbool solve_lra(lp::explanation &ex);
            lbool solve_lia(lp::explanation &ex); 
            bool update_values();
            vector<std::pair<lpvar, rational>> m_to_refine;
            void saturate_basic_linearize();
        public:  
            solver(stellensatz &s) : s(s) {};                
            void init();
            lbool solve(lp::explanation &ex);
            lp::lar_solver &lra() { return *lra_solver; }
            lp::lar_solver const &lra() const { return *lra_solver; }
        };

        solver m_solver;

        struct bound {
            lpvar v = lp::null_lpvar;
            lp::lconstraint_kind k;
            rational rhs;           
        };
        using bound_justification = std::variant<u_dependency*, bound>;
        using bound_justifications = vector<bound_justification>;

        coi m_coi;
        u_map<bound_justifications> m_new_bounds;
        u_map<lp::constraint_index> m_old_constraints;
        indexed_uint_set m_to_refine;
        ptr_vector<u_dependency> m_ci2dep;
        vector<rational> m_values;
        struct eq {
            bool operator()(unsigned_vector const& a, unsigned_vector const& b) const {
                return a == b;
            }
        };
        map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
        u_map<unsigned_vector> m_mon2vars;

        struct resolvent {
            lp::constraint_index old_ci;
            lpvar mi;
            svector<lpvar> xs;
            struct eq {
                bool operator()(resolvent const& a, resolvent const& b) const {
                    return a.old_ci == b.old_ci && a.mi == b.mi && a.xs == b.xs;
                }
            };
            struct hash {
                unsigned operator()(resolvent const& a) const {
                    return hash_u_u(a.old_ci, hash_u_u(a.mi, svector_hash<unsigned_hash>()(a.xs)));
                }
            };
        };
        hashtable<resolvent, resolvent::hash, resolvent::eq> m_resolvents;

        // initialization
        void init_solver();
        void init_vars();
        void init_monomial(unsigned mon_var);

        bool constraint_is_true(lp::constraint_index ci);
        void insert_monomials_from_constraint(lp::constraint_index ci);

        // additional variables and monomials and constraints
        lpvar add_monomial(svector<lp::lpvar> const& vars);
        lp::constraint_index add_ineq(bound_justifications const& bounds, lp::lar_term const &t, lp::lconstraint_kind k, rational const &rhs);
        lp::constraint_index add_ineq(bound_justifications const &bounds, lpvar j, lp::lconstraint_kind k,
                                      rational const &rhs);

        bool is_int(svector<lp::lpvar> const& vars) const;
        rational value(lp::lar_term const &t) const;
        rational value(svector<lpvar> const &prod) const;
        lpvar add_var(bool is_int);
        lbool add_bounds(svector<lpvar> const &vars, bound_justifications &bounds);
        void saturate_constraints();
        void saturate_constraint(lp::constraint_index con_id, lp::lpvar mi, svector<lpvar> const & xs);
        void saturate_basic_linearize();
        void saturate_basic_linearize(lpvar j, rational const &val_j, svector<lpvar> const &vars,
                                      rational const &val_vars);
        void saturate_signs(lpvar j, rational const& val_j, svector<lpvar> const& vars, rational const& val_vars);
        void saturate_units(lpvar j, svector<lpvar> const &vars);
        void saturate_monotonicity(lpvar j, rational const &val_j, svector<lpvar> const &vars, rational const &val_vars);
        void saturate_monotonicity(lpvar j, rational const & val_j, lpvar x, int sign_x, lpvar y, int sign_y);
        void saturate_monotonicity(lpvar j, rational const &val_j, lpvar x, lpvar y);

        void saturate_squares(lpvar j, rational const &val_j, svector<lpvar> const &vars);


        // lemmas
        void add_lemma(lp::explanation const& ex);
        indexed_uint_set m_processed_constraints;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, vector<std::pair<rational, lpvar>> const& lhs,
                                         lp::lconstraint_kind k, rational const& rhs) const;

    public:
        stellensatz(core* core);
        lbool saturate();
    };

}
