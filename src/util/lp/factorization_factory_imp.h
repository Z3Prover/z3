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
#pragma once
#include "util/lp/factorization.h"
namespace nla {
    class  core;
    class signed_vars;

    struct factorization_factory_imp: factorization_factory {
        const core&  m_core;
        const monomial & m_mon;
        const signed_vars& m_rm;
        
        factorization_factory_imp(const signed_vars& rm, const core& s);
        bool find_rm_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const;
        const monomial* find_monomial_of_vars(const svector<lpvar>& vars) const;
    };
}
