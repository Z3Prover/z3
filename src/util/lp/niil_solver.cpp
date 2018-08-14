/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#include "util/lp/niil_solver.h"
#include "util/map.h"
#include "util/lp/mon_eq.h"
namespace niil {

typedef nra::mon_eq mon_eq;

struct solver::imp {
    vector<mon_eq>                                         m_monomials;
    unsigned_vector                                        m_monomials_lim;
    lp::lar_solver&                                        m_lar_solver;
    std::unordered_map<lp::var_index, svector<unsigned>>   m_var_to_monomials;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        : m_lar_solver(s)
        // m_limit(lim),
        // m_params(p)
    {
    }

    void add(lp::var_index v, unsigned sz, lp::var_index const* vs) {
        m_monomials.push_back(mon_eq(v, sz, vs));
    }

    void push() {
        m_monomials_lim.push_back(m_monomials.size());
    }
    void pop(unsigned n) {
        if (n == 0) return;
        m_monomials.shrink(m_monomials_lim[m_monomials_lim.size() - n]);
        m_monomials_lim.shrink(m_monomials_lim.size() - n);       
    }

    bool check_monomial(const mon_eq& m) {
        SASSERT(m_lar_solver.get_column_value(m.var()).is_int());
        const rational & model_val = m_lar_solver.get_column_value_rational(m.var());
        rational r(1);
        for (auto j : m.m_vs) {
            r *= m_lar_solver.get_column_value_rational(j);
        }
        return r == model_val;
    }

    bool generate_basic_lemma_for_mon_sign(const mon_eq& m, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon_zero(const mon_eq& m, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon_neutral(const mon_eq& m, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon_proportionality(const mon_eq& m, lemma& l) {
        return false;
    }

    bool generate_basic_lemma_for_mon(const mon_eq& m, lemma & l) {
        return generate_basic_lemma_for_mon_sign(m, l)
            || generate_basic_lemma_for_mon_zero(m, l)
            || generate_basic_lemma_for_mon_neutral(m, l)
            || generate_basic_lemma_for_mon_proportionality(m, l);
    }

    bool generate_basic_lemma(lemma & l, svector<unsigned> & to_refine) {
        for (unsigned i : to_refine)
            if (generate_basic_lemma_for_mon(m_monomials[i], l))
                return true;
        return false;
    }

    void map_monominals_vars(unsigned i) {
        const mon_eq& m = m_monomials[i];
        for (lp::var_index j : m.m_vs) {
            auto it = m_var_to_monomials.find(j);
            if (it == m_var_to_monomials.end()) {
                auto vect = svector<unsigned>();
                vect.push_back(i);
                m_var_to_monomials[j] = vect;
            }
            else {
                it->second.push_back(i);
            }
        }
    }
    
    void map_var_to_monomials() {
        for (unsigned i = 0; i < m_monomials.size(); i++)
            map_monominals_vars(i);
    }
    
    void init_search() {
        map_var_to_monomials();
    }
    
    lbool check(lemma& l) {
        lp_assert(m_lar_solver.get_status() == lp::lp_status::OPTIMAL);
        svector<unsigned> to_refine;
        for (unsigned i = 0; i < m_monomials.size(); i++) {
            if (!check_monomial(m_monomials[i]))
                to_refine.push_back(i);
        }
        std::cout << "to_refine size = " << to_refine.size() << std::endl;
        if (to_refine.size() == 0)
            return l_true;

        init_search();
        
        if (generate_basic_lemma(l, to_refine))
            return l_true;
        
        return l_undef;
    }
    
};
void solver::add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs) {
    std::cout << "called add_monomial\n";
}

bool solver::need_check() { return true; }

lbool solver::check(lemma& l) {
    return m_imp->check(l);
}


void solver::push(){
    m_imp->push();
}
void solver::pop(unsigned n) {
    m_imp->pop(n);
}


solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_imp = alloc(imp, s, lim, p);
}


}
