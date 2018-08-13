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

    vector<mon_eq>         m_monomials;
    unsigned_vector        m_monomials_lim;
    lp::lar_solver&        m_solver;
    imp(lp::lar_solver& s, reslimit& lim, params_ref const& p)
        : m_solver(s)
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

    lbool check(lp::explanation_t& ex) {
        lp_assert(m_solver.get_status() == lp::lp_status::OPTIMAL);
        return l_undef;
    }
    
};
void solver::add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs) {
    std::cout << "called add_monomial\n";
}

bool solver::need_check() { return true; }

lbool solver::check(lp::explanation_t& ex) {
    return m_imp->check(ex);
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
