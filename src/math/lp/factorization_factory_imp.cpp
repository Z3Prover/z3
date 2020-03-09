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
#include "math/lp/factorization_factory_imp.h"
#include "math/lp/nla_core.h"
namespace nla {
        
factorization_factory_imp::factorization_factory_imp(const monic& rm, const core& s) :
    factorization_factory(rm.rvars(), &s.emons()[rm.var()]),
    m_core(s), m_mon(s.emons()[rm.var()]), m_rm(rm) { }
        
bool factorization_factory_imp::find_canonical_monic_of_vars(const svector<lpvar>& vars, unsigned & i) const {
    return m_core.find_canonical_monic_of_vars(vars, i);
}
bool factorization_factory_imp::canonize_sign(const monic& m) const {
    return m_core.canonize_sign(m);
}
bool factorization_factory_imp::canonize_sign(const factorization& f) const {
    return m_core.canonize_sign(f);
}

}
