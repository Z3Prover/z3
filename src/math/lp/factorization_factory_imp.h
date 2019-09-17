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
#include "math/lp/factorization.h"
namespace nla {
    class  core;

    struct factorization_factory_imp: factorization_factory {
        const core&  m_core;
        const monic & m_mon;
        const monic& m_rm;
        
        factorization_factory_imp(const monic& rm, const core& s);
        bool find_canonical_monic_of_vars(const svector<lpvar>& vars, unsigned & i) const;
        virtual bool canonize_sign(const monic& m) const;
        virtual bool canonize_sign(const factorization& m) const;
 };
}
