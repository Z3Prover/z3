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
#include "util/lp/factorization_factory_imp.h"
#include "util/lp/nla_core.h"
namespace nla {
        
factorization_factory_imp::factorization_factory_imp(const smon& rm, const core& s) :
    factorization_factory(rm.rvars(), &s.m_emons[rm.var()]),
    m_core(s), m_mon(s.m_emons[rm.var()]), m_rm(rm) { }
        
bool factorization_factory_imp::find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const {
    return m_core.find_rm_monomial_of_vars(vars, i);
}
const monomial* factorization_factory_imp::find_monomial_of_vars(const svector<lpvar>& vars) const {
    return m_core.find_monomial_of_vars(vars);
}
}
