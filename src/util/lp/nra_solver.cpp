/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/lp/nra_solver.h"
#include "nlsat/nlsat_solver.h"

namespace lp {

    struct nra_solver::imp {
        lean::lar_solver& s;
        reslimit      m_limit;  // TBD: extract from lar_solver
        params_ref    m_params; // TBD: pass from outside

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
            // add polynomial definitions.
            for (auto const& m : m_monomials) {
                add_monomial_eq(solver, m);
            }
            lbool r = solver.check();
            if (r == l_true) {
                // TBD extract model.
            }
            return r;
        }                

        void add_monomial_eq(nlsat::solver& solver, mon_eq const& m) {
            
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
