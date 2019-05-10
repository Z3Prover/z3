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

    struct factorization_factory_imp: factorization_factory {
        const core&  m_core;
        const monomial & m_mon;
        const monomial& m_rm;
        
        factorization_factory_imp(const monomial& rm, const core& s);
        bool find_canonical_monomial_of_vars(const svector<lpvar>& vars, unsigned & i) const;
        virtual bool canonize_sign(const monomial& m) const;
        virtual bool canonize_sign(const factorization& m) const;
 };
}
