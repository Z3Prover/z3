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
#include "math/lp/nla_intervals.h"
#include "math/lp/nex.h"
#include "math/lp/cross_nested.h"
#include "math/lp/int_set.h"

namespace nla {
class core;


class horner : common {
    nex_creator::sum_factory  m_row_sum;
    unsigned         m_row_index;                      
public:
    typedef intervals::interval interv;
    horner(core *core, intervals*);
    bool horner_lemmas();
    template <typename T> // T has an iterator of (coeff(), var())
    bool lemmas_on_row(const T&);
    template <typename T>  bool row_is_interesting(const T&) const;

    
    intervals::interval interval_of_sum_with_deps(const nex_sum*);
    intervals::interval interval_of_sum_no_term_with_deps(const nex_sum*);
    void set_var_interval_with_deps(lpvar j, intervals::interval&) const;
    bool lemmas_on_expr(cross_nested&, nex_sum*);
    
    template <typename T> // T has an iterator of (coeff(), var())
    bool row_has_monomial_to_refine(const T&) const;
    bool interval_from_term_with_deps(const nex* e, interv&) const;
}; // end of horner
}
