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
#include "math/lp/nla_expr.h"

namespace nla {
class core;


class horner : common {   
    intervals m_intervals;
public:
    
    horner(core *core);
    void horner_lemmas();
    template <typename T> // T has an iterator of (coeff(), var())
    void lemma_on_row(const T&);
    template <typename T>
    bool row_is_interesting(const T&) const;
    template <typename T> nla_expr<rational> create_expr_from_row(const T&);
    intervals::interval interval_of_expr(const nla_expr<rational>& e);
    void check_interval_for_conflict(const intervals::interval&);
    nla_expr<rational> nexvar(lpvar j) const;
    nla_expr<rational> cross_nested_of_sum(const nla_expr<rational>&);    
    void get_occurences_map(const nla_expr<rational>& e,
                            std::unordered_map<unsigned, lpvar>& ) const;
    unsigned random_most_occured_var(std::unordered_map<lpvar, unsigned>& occurences);
    nla_expr<rational> split_with_var(const nla_expr<rational> &, lpvar);
    void set_var_interval(lpvar j, intervals::interval&);
}; // end of horner
}
