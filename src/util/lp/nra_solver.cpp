/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/lp/nra_solver.h"

namespace lp {

    struct nra_solver::imp {
        lean::lar_solver& s;

        svector<lean::var_index>         m_vars;
        vector<svector<lean::var_index>> m_monomials;
        unsigned_vector                  m_lim;

        imp(lean::lar_solver& s): s(s) {
            m_lim.push_back(0);
        }

        lean::final_check_status check_feasible() {
            return lean::final_check_status::GIVEUP;
        }

        void add(lean::var_index v, unsigned sz, lean::var_index const* vs) {
            m_vars.push_back(v);
            m_monomials.push_back(svector<lean::var_index>(sz, vs));
        }

        void push() {
            m_lim.push_back(m_vars.size());
        }

        void pop(unsigned n) {
            SASSERT(n < m_lim.size());
            m_lim.shrink(m_lim.size() - n);       
            m_vars.shrink(m_lim.back());
            m_monomials.shrink(m_lim.back());
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
