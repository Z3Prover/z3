/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "math/lp/nla_coi.h"
#include "math/lp/int_solver.h"
#include "math/polynomial/polynomial.h"
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
            lbool solve(lp::explanation &ex, vector<ineq>& ineqs);
            lp::lar_solver &lra() { return *lra_solver; }
            lp::lar_solver const &lra() const { return *lra_solver; }
        };

        solver m_solver;

        struct bound {
            lpvar v = lp::null_lpvar;
            lp::lconstraint_kind k;
            rational rhs;           
        };
        using assumption = std::variant<u_dependency*, bound, lp::constraint_index>;
        using assumptions = vector<assumption>;

        coi m_coi;
        u_map<assumptions> m_assumptions;  // map from constraint to set of assumptions
        indexed_uint_set m_monomials_to_refine;
        indexed_uint_set m_false_constraints;  // constraints that are false in the current model
        vector<rational> m_values;
        struct eq {
            bool operator()(unsigned_vector const& a, unsigned_vector const& b) const {
                return a == b;
            }
        };
        map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
        u_map<unsigned_vector> m_mon2vars;
        bool is_mon_var(lpvar v) const { return m_mon2vars.contains(v); }
        lpvar find_max_lex_monomial(lp::lar_term const &t) const;
        bool is_lex_greater(svector<lpvar> const &a, svector<lpvar> const &b) const;
        
        unsigned m_max_monomial_degree = 0;

        vector<svector<lp::constraint_index>> m_occurs; // map from variable to constraints they occur. 

        // for factoring
        small_object_allocator m_allocator;
        unsynch_mpq_manager m_qm;
        polynomial::manager m_pm;

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
        void init_occurs();
        void init_occurs(lp::constraint_index ci);

        bool constraint_is_true(lp::constraint_index ci) const;
        void insert_monomials_from_constraint(lp::constraint_index ci);

        // additional variables and monomials and constraints
        using term_offset = std::pair<lp::lar_term, rational>;  // term and its offset
        lpvar add_monomial(svector<lp::lpvar> const& vars);
        lpvar add_term(term_offset &t);
        lp::constraint_index add_ineq(char const* rule, assumptions const& bounds, lp::lar_term const &t, lp::lconstraint_kind k, rational const &rhs);
        lp::constraint_index add_ineq(char const* rule, assumptions const &bounds, lpvar j, lp::lconstraint_kind k,
                                      rational const &rhs);

        bool is_int(svector<lp::lpvar> const& vars) const;
        rational value(lp::lar_term const &t) const;
        rational value(svector<lpvar> const &prod) const;
        lpvar add_var(bool is_int);
        lbool add_bounds(svector<lpvar> const &vars, assumptions &bounds);
        void saturate_constraints();
        lp::constraint_index saturate_constraint(lp::constraint_index con_id, lp::lpvar mi, svector<lpvar> const & xs);
        
        void resolve(lpvar j, lp::constraint_index ci1, lp::constraint_index ci2);
        void saturate_basic_linearize();
        void saturate_basic_linearize(lpvar j, rational const &val_j, svector<lpvar> const &vars,
                                      rational const &val_vars);
        void saturate_signs(lpvar j, rational const& val_j, svector<lpvar> const& vars, rational const& val_vars);
        void saturate_units(lpvar j, svector<lpvar> const &vars);
        void saturate_monotonicity(lpvar j, rational const &val_j, svector<lpvar> const &vars, rational const &val_vars);
        void saturate_monotonicity(lpvar j, rational const & val_j, lpvar x, int sign_x, lpvar y, int sign_y);
        void saturate_monotonicity(lpvar j, rational const &val_j, lpvar x, lpvar y);
        void saturate_squares(lpvar j, rational const &val_j, svector<lpvar> const &vars);

        // polynomial tricks
        uint_set m_factored_constraints;
        bool get_factors(term_offset &t, vector<std::pair<term_offset, unsigned>> &factors);
        polynomial::polynomial_ref to_poly(term_offset const &t);
        term_offset to_term(polynomial::polynomial const &p);
        bool saturate_factors(lp::constraint_index ci, lp::explanation& ex, vector<ineq>& ineqs);
        bool saturate_factors(lp::explanation& ex, vector<ineq>& ineqs);

        // lemmas
        void add_lemma(lp::explanation const& ex, vector<ineq> const& ineqs);
        indexed_uint_set m_constraints_in_conflict;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);

        std::ostream& display(std::ostream& out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, lp::lar_term const& lhs,
                                         lp::lconstraint_kind k, rational const& rhs) const;
        std::ostream& display(std::ostream &out, term_offset const &t) const;
        std::ostream& display(std::ostream &out, assumptions const &bounds) const;

    public:
        stellensatz(core* core);
        lbool saturate();
    };

}
