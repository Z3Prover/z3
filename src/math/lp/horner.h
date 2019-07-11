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
    typedef nla_expr<rational> nex;
    intervals m_intervals;
public:
    
    horner(core *core);
    void horner_lemmas();
    template <typename T> // T has an iterator of (coeff(), var())
    void lemmas_on_row(const T&);
    template <typename T>  bool row_is_interesting(const T&) const;
    template <typename T> nex create_sum_from_row(const T&);
    intervals::interval interval_of_expr(const nex& e);
    
    nex nexvar(lpvar j) const;
    nex cross_nested_of_sum(const nex&, lpvar);    
    vector<lpvar> get_mult_occurences(const nex& e) const;
    void split_with_var(nex &, lpvar, vector<nex*> & front);
    void set_var_interval(lpvar j, intervals::interval&);
    intervals::interval interval_of_sum(const vector<nex>&);
    intervals::interval interval_of_mul(const vector<nex>&);
    void set_interval_for_scalar(intervals::interval&, const rational&);
    std::set<lpvar> get_vars_of_expr(const nex &) const;
    void lemmas_on_expr(nex &);
    void cross_nested_of_expr_on_front_elem(nex& , nex*, vector<nex*>& front);
    void cross_nested_of_expr_on_sum_and_var(nex& , nex*, lpvar, vector<nex*>& front);    
    bool can_be_cross_nested_more(const nex&) const;
}; // end of horner
}
