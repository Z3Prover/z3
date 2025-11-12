/*++
  Copyright (c) 2025 Microsoft Corporation

  --*/
#pragma once

#include "util/scoped_ptr_vector.h"
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
            lp::explanation m_ex;
            vector<ineq> m_ineqs;
            lbool solve_lra();
            lbool solve_lia(); 
            bool update_values();
            vector<std::pair<lpvar, rational>> m_to_refine;
            void saturate_basic_linearize();
        public:  
            solver(stellensatz &s) : s(s) {};                
            void init();
            lbool solve();
            lp::lar_solver &lra() { return *lra_solver; }
            lp::lar_solver const &lra() const { return *lra_solver; }
            lp::explanation &ex() { return m_ex; }
            vector<ineq> &ineqs() { return m_ineqs; }
        };

        solver m_solver;

        // factor t into coeff*x^degree*p + q, such that degree(x, q) < degree, 
        struct factorization {
            rational coeff;
            unsigned degree;
            lp::lar_term p;
            lp::lar_term q;
        };

        struct external_justification {
            u_dependency *dep = nullptr;
            external_justification(u_dependency *d) : dep(d) {}
        };
        struct assumption_justification {         
        };
        struct addition_justification {
            lp::constraint_index left, right;
        };
        struct multiplication_const_justification {
            lp::constraint_index ci;
            rational mul;
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
            multiplication_const_justification, 
            multiplication_justification
        >;

        coi m_coi;
        scoped_ptr_vector<justification> m_justifications;
        void add_justification(lp::constraint_index ci, justification const &j) {
            VERIFY(ci == m_justifications.size());
            m_justifications.push_back(alloc(justification, j));
        }
        vector<rational> m_values;
        struct eq {
            bool operator()(unsigned_vector const& a, unsigned_vector const& b) const {
                return a == b;
            }
        };
        map<unsigned_vector, unsigned, svector_hash<unsigned_hash>, eq> m_vars2mon;
        u_map<unsigned_vector> m_mon2vars;
        bool is_mon_var(lpvar v) const { return m_mon2vars.contains(v); }
        
        unsigned m_max_monomial_degree = 0;

        vector<svector<lp::constraint_index>> m_occurs; // map from variable to constraints they occur. 

        bool is_new_inequality(vector<std::pair<rational, lpvar>> lhs, lp::lconstraint_kind k, rational const &rhs);


        // initialization
        void init_solver();
        void init_vars();
        void init_monomial(unsigned mon_var);
        void init_occurs();
        void init_occurs(lp::constraint_index ci);

        void eliminate_variables();
        lp::lpvar select_variable_to_eliminate(lp::constraint_index ci);
        unsigned degree_of_var_in_constraint(lpvar v, lp::constraint_index ci) const;
        unsigned degree_of_var_in_monomial(lpvar v, lpvar mi) const;
        factorization factor(lpvar v, lp::constraint_index ci);
        lp::lpvar divide(lpvar v, unsigned degree, lpvar mi);

        bool constraint_is_true(lp::constraint_index ci) const;

        // additional variables and monomials and constraints
        using term_offset = std::pair<lp::lar_term, rational>;  // term and its offset

        svector<lp::lpvar> expand_monomial(svector<lp::lpvar> const & vars);
        lpvar mk_monomial(svector<lp::lpvar> const& vars);
        lpvar mk_monomial(svector<lp::lpvar> const &vars, lp::lpvar j);
        lpvar mk_term(term_offset &t);

        void gcd_normalize(vector<std::pair<rational, lpvar>> &t, lp::lconstraint_kind k, rational &rhs);
        lp::constraint_index add_ineq(justification const& just, lp::lar_term &t, lp::lconstraint_kind k, rational const &rhs);

        lp::constraint_index add_ineq(justification const &just, lpvar j, lp::lconstraint_kind k,
                                      rational const &rhs);

        lp::constraint_index assume(lp::lar_term &t, lp::lconstraint_kind k, rational const &rhs);
        lp::constraint_index normalize_ineq(lp::constraint_index ci);
        lp::constraint_index add(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply(lp::constraint_index ci, rational const &mul);
        lp::constraint_index multiply(lp::constraint_index left, lp::constraint_index right);
        lp::constraint_index multiply_var(lp::constraint_index ci, lpvar x);

        bool is_int(svector<lp::lpvar> const& vars) const;
        rational cvalue(lp::lar_term const &t) const;
        rational mvalue(lp::lar_term const &t) const;
        rational cvalue(svector<lpvar> const &prod) const;
        rational mvalue(svector<lpvar> const &prod) const;
        lpvar add_var(bool is_int);

        // lemmas
        void add_lemma();
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
        std::ostream& display_constraint(std::ostream& out, lp::lar_term const& lhs,
                                         lp::lconstraint_kind k, rational const& rhs) const;
        std::ostream& display(std::ostream &out, term_offset const &t) const;
        std::ostream& display(std::ostream &out, justification const &bounds) const;
        std::ostream &display_var(std::ostream &out, lpvar j) const;
        std::ostream &display_lemma(std::ostream &out, lp::explanation const &ex, vector<ineq> const &ineqs);

    public:
        stellensatz(core* core);
        lbool saturate();
    };

}
