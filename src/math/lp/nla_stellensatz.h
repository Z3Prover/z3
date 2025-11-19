/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "util/scoped_ptr_vector.h"
#include "math/dd/dd_pdd.h"
#include "math/lp/nla_coi.h"
#include "math/lp/int_solver.h"
#include <variant>

namespace nla {

    class core; 
    class lar_solver;
    class stellensatz : common {

        struct external_justification {
            u_dependency *dep = nullptr;
            external_justification(u_dependency *d) : dep(d) {}
        };
        struct assumption_justification {};
        struct addition_justification {
            lp::constraint_index left, right;
        };
        struct multiplication_poly_justification {
            lp::constraint_index ci;
            dd::pdd p;
        };
        struct multiplication_justification {
            lp::constraint_index left, right;
        };
        struct division_justification {
            lp::constraint_index ci;
            lp::constraint_index divisor;
        };
        struct substitute_justification {
            lp::constraint_index ci;
            lp::constraint_index ci_eq;            
            lpvar   v;
            dd::pdd p;
        };
        struct eq_justification {
            lp::constraint_index left;
            lp::constraint_index right;
        };
        struct gcd_justification {
            lp::constraint_index ci;
        };
        struct propagation_justification {
            svector<lp::constraint_index> cs;
        };

        using justification = std::variant<
            external_justification, 
            assumption_justification, 
            gcd_justification, 
            substitute_justification,
            addition_justification,
            division_justification,
            eq_justification,
            propagation_justification,
            multiplication_poly_justification, 
            multiplication_justification>;

        struct constraint {
            dd::pdd p;
            lp::lconstraint_kind k;
            justification j;
        };

        class monomial_factory {
            struct eq {
                bool operator()(unsigned_vector const &a, unsigned_vector const &b) const {
                    return a == b;
                }
            };
            map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
            u_map<unsigned_vector> m_mon2vars;
            bool is_mon_var(lpvar v) const {
                return m_mon2vars.contains(v);
            }

        public:
            void reset() {
                m_vars2mon.reset();
                m_mon2vars.reset();
            }

            lpvar mk_monomial(lp::lar_solver& lra, svector<lpvar> const &vars);

            lpvar get_monomial(svector<lpvar> const &vars);

            void init(lpvar v, svector<lpvar> const &_vars);
        };

        using term_offset = std::pair<lp::lar_term, rational>;

        class solver {            
            stellensatz &s;
            scoped_ptr<lp::lar_solver> lra_solver;
            scoped_ptr<lp::int_solver> int_solver;
            lp::explanation m_ex;
            unsigned_vector m_internal2external_constraints;
            monomial_factory m_monomial_factory;
            lbool solve_lra();
            lbool solve_lia(); 

            void init();
            term_offset to_term_offset(dd::pdd const &p);
        public:  
            solver(stellensatz &s) : s(s) {};                
            lbool solve(svector<lp::constraint_index>& core);
            void update_values(vector<rational>& values);
        };

        solver m_solver;


        // factor t into x^degree*p + q, such that degree(x, q) < degree, 
        struct factorization {
            unsigned degree;
            dd::pdd p, q;
        };


        coi m_coi;
        dd::pdd_manager pddm;
        vector<constraint> m_constraints;
        monomial_factory m_monomial_factory;
        indexed_uint_set m_active;
        vector<uint_set> m_tabu;
        vector<rational> m_values;
        svector<lp::constraint_index> m_core, m_occurs_trail;

        struct constraint_key {
            unsigned pdd;
            lp::lconstraint_kind k;
            struct eq {
                bool operator()(constraint_key const &a, constraint_key const &b) const {
                    return a.pdd == b.pdd && a.k == b.k;
                }
            };
            struct hash {
                unsigned operator()(constraint_key const &c) const {
                    return hash_u_u(c.pdd, static_cast<unsigned>(c.k));
                }            
            };
        };
        map<constraint_key, lp::constraint_index, constraint_key::hash, constraint_key::eq> m_constraint_index;


        dd::pdd to_pdd(lpvar v);
        void init_monomial(unsigned mon_var); 
        term_offset to_term_offset(dd::pdd const &p);
        bool has_term_offset(dd::pdd const &p);

        lp::constraint_index add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j);
        
        lp::constraint_index add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const &rhs, justification j);
        
        vector<svector<lp::constraint_index>> m_occurs; // map from variable to constraints they occur. 

        // initialization
        void init_solver();
        void init_vars();
        void init_occurs();
        void init_occurs(lp::constraint_index ci);
        void remove_occurs(lp::constraint_index ci);

        lbool conflict_saturation();
        lbool factor(lp::constraint_index ci);
        bool conflict(lp::constraint_index ci);
        void conflict(svector<lp::constraint_index> const& core);
        bool vanishing(lpvar x, factorization const& f, lp::constraint_index ci);
        lp::lpvar select_variable_to_eliminate(lp::constraint_index ci);
        unsigned degree_of_var_in_constraint(lpvar v, lp::constraint_index ci) const;
        factorization factor(lpvar v, lp::constraint_index ci);  
        bool resolve_variable(lpvar x, lp::constraint_index ci);
        bool resolve_variable(lpvar x, lp::constraint_index ci, lp::constraint_index other_ci, rational const& p_value, 
            factorization const& f, unsigned_vector const& m1, dd::pdd _f_p);

        lbool model_repair();
        bool model_repair(lp::lpvar v);
        struct bound_info {
            rational value;
            lp::constraint_index bound = lp::null_ci;
            svector<lp::constraint_index> bounds;
        };
        std::pair<bound_info, bound_info> find_bounds(lpvar v);
        bool assume_ge(lpvar v, lp::constraint_index lo, lp::constraint_index hi);

        bool constraint_is_true(lp::constraint_index ci) const;
        bool is_new_constraint(lp::constraint_index ci) const;

        lp::constraint_index gcd_normalize(lp::constraint_index ci);
        lp::constraint_index assume(dd::pdd const& p, lp::lconstraint_kind k);
        lp::constraint_index add(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply(lp::constraint_index ci, dd::pdd p);
        lp::constraint_index multiply(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index divide(lp::constraint_index ci, lp::constraint_index divisor, dd::pdd d);
        lp::constraint_index substitute(lp::constraint_index ci, lp::constraint_index ci_eq, lpvar v, dd::pdd p);

        bool is_int(svector<lp::lpvar> const& vars) const;
        bool is_int(dd::pdd const &p) const;
        rational value(dd::pdd const& p) const;
        rational value(lp::lpvar v) const { return m_values[v]; }

        void add_active(lp::constraint_index ci, uint_set const &tabu);

        // lemmas
        indexed_uint_set m_constraints_in_conflict;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);
        void explain_constraint(lp::constraint_index ci, svector<lp::constraint_index> &external,
                                svector<lp::constraint_index> &assumptions);
        bool backtrack(svector<lp::constraint_index> const& core);

        struct pp_j {
            stellensatz const &s;
            lpvar j;
            pp_j(stellensatz const&s, lpvar j) : s(s), j(j) {}
            std::ostream &display(std::ostream &out) const {
                return s.display_var(out, j);
            }
        };
        friend std::ostream &operator<<(std::ostream &out, pp_j const &p) {
            return p.display(out);
        }
        std::ostream& display(std::ostream& out) const;
        std::ostream& display_product(std::ostream& out, svector<lpvar> const& vars) const;
        std::ostream& display_constraint(std::ostream& out, lp::constraint_index ci) const;
        std::ostream& display_constraint(std::ostream& out, constraint const& c) const;
        std::ostream &display(std::ostream &out, justification const &j) const;
        std::ostream &display_var(std::ostream &out, lpvar j) const;
        std::ostream &display_lemma(std::ostream &out, lp::explanation const &ex);
        std::ostream &display(std::ostream &out, term_offset const &t) const;

    public:
        stellensatz(core* core);
        lbool saturate();
    };

}
