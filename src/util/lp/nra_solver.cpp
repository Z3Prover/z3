/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/lp/nra_solver.h"
#include "nlsat/nlsat_solver.h"
#include "math/polynomial/polynomial.h"
#include "util/map.h"

namespace lp {

    struct nra_solver::imp {
        lean::lar_solver& s;
        reslimit      m_limit;  // TBD: extract from lar_solver
        params_ref    m_params; // TBD: pass from outside
        u_map<polynomial::var> m_lp2nl;  // map from lar_solver variables to nlsat::solver variables

        struct mon_eq {
            mon_eq(lean::var_index v, svector<lean::var_index> const& vs):
                m_v(v), m_vs(vs) {}
            lean::var_index          m_v;
            svector<lean::var_index> m_vs;
        };

        vector<mon_eq>                   m_monomials;
        unsigned_vector                  m_lim;
        mutable std::unordered_map<lean::var_index, rational> m_variable_values; // current model

        imp(lean::lar_solver& s): 
            s(s) {
        }

        lean::final_check_status check_feasible() {
            return lean::final_check_status::GIVEUP;
        }

        void add(lean::var_index v, unsigned sz, lean::var_index const* vs) {
            m_monomials.push_back(mon_eq(v, svector<lean::var_index>(sz, vs)));
        }

        void push() {
            m_lim.push_back(m_monomials.size());
        }

        void pop(unsigned n) {
            if (n == 0) return;
            SASSERT(n < m_lim.size());
            m_monomials.shrink(m_lim[m_lim.size() - n]);
            m_lim.shrink(m_lim.size() - n);       
        }

        /*
          \brief Check if polynomials are well defined.
          multiply values for vs and check if they are equal to value for v.
          epsilon has been computed.
        */
        bool check_assignment(mon_eq const& m) const {
            rational r1 = m_variable_values[m.m_v];
            rational r2(1);
            for (auto w : m.m_vs) {
                r2 *= m_variable_values[w];
            }
            return r1 == r2;
        }

        bool check_assignments() const {
            s.get_model(m_variable_values);
            for (auto const& m : m_monomials) {
                if (!check_assignment(m)) return false;
            }
            return true;
        }


        /**
           \brief one-shot nlsat check.
           A one shot checker is the least functionality that can 
           enable non-linear reasoning. 
           In addition to checking satisfiability we would also need
           to identify equalities in the model that should be assumed
           with the remaining solver.
           
           TBD: use partial model from lra_solver to prime the state of nlsat_solver.
        */
        lbool check_nlsat() {
            nlsat::solver solver(m_limit, m_params);
            // add linear inequalities from lra_solver
            for (unsigned i = 0; i < s.constraint_count(); ++i) {
                add_constraint(solver, s.get_constraint(i));
            }
            // add polynomial definitions.
            for (auto const& m : m_monomials) {
                add_monomial_eq(solver, m);
            }
            lbool r = solver.check(); // TBD: get assumptions from literals that are asserted above level 0.
            if (r == l_true) {
                // TBD extract model.
                // check interface equalities
            }
            return r;
        }                

        void add_monomial_eq(nlsat::solver& solver, mon_eq const& m) {
            polynomial::manager& pm = solver.pm();
            svector<polynomial::var> vars;
            for (auto v : m.m_vs) {
                vars.push_back(lp2nl(solver, v));
            }
            polynomial::monomial_ref m1(pm.mk_monomial(vars.size(), vars.c_ptr()), pm);
            polynomial::monomial_ref m2(pm.mk_monomial(lp2nl(solver, m.m_v), 1), pm);
            polynomial::monomial* mls[2] = { m1, m2 };
            polynomial::scoped_numeral_vector coeffs(pm.m());
            coeffs.push_back(mpz(1));
            coeffs.push_back(mpz(-1));
            polynomial::polynomial_ref p(pm.mk_polynomial(2, coeffs.c_ptr(), mls),  pm);
            polynomial::polynomial* ps[1] = { p };
            bool even[1] = { false };
            nlsat::literal lit = solver.mk_ineq_literal(nlsat::atom::kind::EQ, 1, ps, even);
            solver.mk_clause(1, &lit, 0);
        }

        void add_constraint(nlsat::solver& solver, lean::lar_base_constraint const& c) {
            polynomial::manager& pm = solver.pm();
            auto k = c.m_kind;
            auto rhs = c.m_right_side;
            auto lhs = c.get_left_side_coefficients();
            unsigned sz = lhs.size();
            svector<polynomial::var> vars;
            rational den = denominator(rhs);
            for (auto kv : lhs) {
                vars.push_back(lp2nl(solver, kv.second));
                den = lcm(den, denominator(kv.first));
            }
            vector<rational> coeffs;
            for (auto kv : lhs) {
                coeffs.push_back(den * kv.first);
            }
            rhs *= den;
            polynomial::polynomial_ref p(pm.mk_linear(sz, coeffs.c_ptr(), vars.c_ptr(), -rhs), pm);
            nlsat::literal lit;
            switch (k) {
            case lean::lconstraint_kind::LE:
                // lit = ~solver.mk_ineq_literal(nlsat::atom::kind::GT, );
                break;
            case lean::lconstraint_kind::GE:
            case lean::lconstraint_kind::LT:
            case lean::lconstraint_kind::GT:
            case lean::lconstraint_kind::EQ:
                break;
            }

            // solver.mk_clause();

            // c.get_free_coeff_of_left_side();
        }

        
        // translate var_index into polynomial::var that are declared on nlsat::solver.
        

        polynomial::var lp2nl(nlsat::solver& solver, lean::var_index v) {
            polynomial::var r;
            if (!m_lp2nl.find(v, r)) {
                r = solver.mk_var(false); // TBD: is it s.column_is_integer(v), if then the function should take a var_index and not unsigned; s.is_int(v);
                m_lp2nl.insert(v, r);
            }
            return r;
        }
    };

    nra_solver::nra_solver(lean::lar_solver& s) {
        m_imp = alloc(imp, s);
    }

    nra_solver::~nra_solver() {
        dealloc(m_imp);
    }

    void nra_solver::add_monomial(lean::var_index v, unsigned sz, lean::var_index const* vs) {
        m_imp->add(v, sz, vs);
    }

    lean::final_check_status nra_solver::check_feasible() {
        return m_imp->check_feasible();
    }

    void nra_solver::push() {
        m_imp->push();
    }

    void nra_solver::pop(unsigned n) {
        m_imp->pop(n);
    }
}
