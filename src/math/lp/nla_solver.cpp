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
#include "math/lp/nla_solver.h"
#include <map>
#include "math/lp/monic.h"
#include "math/lp/lp_utils.h"
#include "math/lp/var_eqs.h"
#include "math/lp/factorization.h"
#include "math/lp/nla_solver.h"
namespace nla {

void solver::add_monic(lpvar v, unsigned sz, lpvar const* vs) {
    m_core->add_monic(v, sz, vs);
}

bool solver::is_monic_var(lpvar v) const {
    return m_core->is_monic_var(v);
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
        
solver::solver(lp::lar_solver& s): m_core(alloc(core, s, m_res_limit))  {
}

bool solver::influences_nl_var(lpvar j) const {    
    return m_core->influences_nl_var(j);
}

solver::~solver() {
    dealloc(m_core);
}
}
