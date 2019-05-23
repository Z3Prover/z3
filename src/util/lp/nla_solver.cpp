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
#include "util/lp/nla_solver.h"
#include <map>
#include "util/lp/monomial.h"
#include "util/lp/lp_utils.h"
#include "util/lp/var_eqs.h"
#include "util/lp/factorization.h"
#include "util/lp/nla_solver.h"
namespace nla {

// returns the monomial index
void solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    m_core->add(v, sz, vs);
}

bool solver::need_check() { return true; }

lbool solver::check(vector<lemma>& l) {
    return m_core->check(l);
}

void solver::push(){
    m_core->push();
}

void solver::pop(unsigned n) {
    m_core->pop(n);
}

    std::ostream& solver::display(std::ostream& out) {
        return m_core->print_monomials(out);
    }

        
solver::solver(lp::lar_solver& s) {
    m_core = alloc(core, s);
}

solver::~solver() {
    dealloc(m_core);
}

}
