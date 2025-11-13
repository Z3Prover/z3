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
        struct gcd_justification {
            lp::constraint_index ci;
        };

        using justification = std::variant<
            external_justification, 
            assumption_justification, 
            gcd_justification, 
            addition_justification,
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
            bool update_values();
            void init();
            void add_lemma();
            term_offset to_term_offset(dd::pdd const &p);
        public:  
            solver(stellensatz &s) : s(s) {};                
            lbool solve();
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


        dd::pdd to_pdd(lpvar v);
        void init_monomial(unsigned mon_var); 
        term_offset to_term_offset(dd::pdd const &p);

        lp::constraint_index add_constraint(dd::pdd p, lp::lconstraint_kind k, justification j);
        
        lp::constraint_index add_var_bound(lp::lpvar v, lp::lconstraint_kind k, rational const &rhs, justification j);
        
        vector<svector<lp::constraint_index>> m_occurs; // map from variable to constraints they occur. 

        // initialization
        void init_solver();
        void init_vars();
        void init_occurs();
        void init_occurs(lp::constraint_index ci);

        lbool eliminate_variables();
        lp::lpvar select_variable_to_eliminate(lp::constraint_index ci);
        unsigned degree_of_var_in_constraint(lpvar v, lp::constraint_index ci) const;
        factorization factor(lpvar v, lp::constraint_index ci);    

        bool constraint_is_true(lp::constraint_index ci) const;

        lp::constraint_index gcd_normalize(lp::constraint_index ci);
        lp::constraint_index assume(dd::pdd const& p, lp::lconstraint_kind k);
        lp::constraint_index add(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply(lp::constraint_index ci, dd::pdd p);
        lp::constraint_index multiply(lp::constraint_index left, lp::constraint_index right);

        bool is_int(svector<lp::lpvar> const& vars) const;
        bool is_int(dd::pdd const &p) const;
        rational cvalue(dd::pdd const& p) const;

        // lemmas
        indexed_uint_set m_constraints_in_conflict;
        void explain_constraint(lemma_builder& new_lemma, lp::constraint_index ci, lp::explanation &ex);

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
