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
#include "util/lp/rooted_mons.h"
#include "util/lp/nla_solver.h"
namespace nla {

// returns the monomial index
unsigned solver::add_monomial(lpvar v, unsigned sz, lpvar const* vs) {
    return m_core->add(v, sz, vs);
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
        
solver::solver(lp::lar_solver& s, reslimit& lim, params_ref const& p) {
    m_core = alloc(core, s, lim, p);
}

solver::~solver() {
    dealloc(m_core);
}

}
