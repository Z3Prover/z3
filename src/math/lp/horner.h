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

#include "math/lp/nla_common.h"

namespace nla {
class core;


class horner : common {   
public:
    horner(core *core);
    void horner_lemmas();
    template <typename T> // T has an iterator of (coeff(), var())
    void lemma_on_row(const T&);
    template <typename T>
    bool row_is_interesting(const T&) const;
private:    
}; // end of horner
}
