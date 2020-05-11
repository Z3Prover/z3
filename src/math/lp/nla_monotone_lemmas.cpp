/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/
#include "math/lp/nla_basics_lemmas.h"
#include "math/lp/nla_core.h"
namespace nla {

monotone::monotone(core * c) : common(c) {}

    
void monotone::monotonicity_lemma() {
    unsigned shift = random();
    unsigned size = c().m_to_refine.size();
    for (unsigned i = 0; i < size && !done(); i++) { 
        lpvar v = c().m_to_refine[(i + shift) % size];
        monotonicity_lemma(c().emons()[v]);
    }
}
   
void monotone::monotonicity_lemma(monic const& m) {
    SASSERT(!check_monic(m));
    if (c().mon_has_zero(m.vars()))
        return;
    if (c().has_big_num(m)) 
       return;
    const rational prod_val = abs(c().product_value(m));
    const rational m_val = abs(var_val(m));
    if (m_val < prod_val)
        monotonicity_lemma_lt(m, prod_val);
    else if (m_val > prod_val)
        monotonicity_lemma_gt(m, prod_val);
}

void monotone::monotonicity_lemma_gt(const monic& m, const rational& prod_val) {
    TRACE("nla_solver", tout << "prod_val = " << prod_val << "\n";
          tout << "m = "; c().print_monic_with_vars(m, tout););
    new_lemma lemma(c(), __FUNCTION__);
    for (lpvar j : m.vars()) {
        c().add_abs_bound(lemma, j, llc::GT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(lemma, m_j, llc::LE, prod_val);
}
    
/** \brief enforce the inequality |m| >= product |m[i]| .

    /\_i |m[i]| >= |val(m[i])| => |m| >= |product_i val(m[i])|
    <=>
    \/_i |m[i]| < |val(m[i])} or |m| >= |product_i val(m[i])|
*/
void monotone::monotonicity_lemma_lt(const monic& m, const rational& prod_val) {
    new_lemma lemma(c(), __FUNCTION__);
    for (lpvar j : m.vars()) {
        c().add_abs_bound(lemma, j, llc::LT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(lemma, m_j, llc::GE, prod_val);
}
   

}
