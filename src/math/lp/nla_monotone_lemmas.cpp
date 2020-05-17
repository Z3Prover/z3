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
        monotonicity_lemma_lt(m);
    else if (m_val > prod_val)
        monotonicity_lemma_gt(m);
}

/** \brief enforce the inequality |m| <= product |m[i]| .

    /\_i |m[i]| <= |val(m[i])| => |m| <= |product_i val(m[i])|
    <=>
    \/_i |m[i]| > |val(m[i])| or |m| <= |product_i val(m[i])|

    implied by 
       m[i] > val(m[i])     for val(m[i]) > 0
       m[i] < val(m[i])     for val(m[i]) < 0
       m >= product m[i]    for product m[i] < 0
       m <= product m[i]    for product m[i] > 0

    Example:

    0 >= x >= -2 & 0 <= y <= 3 => x*y >= -6
    0 >= x >= -2 & 0 <= y <= 3 => x*x*y <= 12
    
*/
void monotone::monotonicity_lemma_gt(const monic& m) {
    new_lemma lemma(c(), "monotonicity > ");
    rational product(1);
    for (lpvar j : m.vars()) {
        auto v = c().val(j);
        lemma |= ineq(j, v.is_neg() ? llc::LT : llc::GT, v);
        lemma |= ineq(j, v.is_neg() ? llc::GT : llc::LT, 0);
        product *= v;
    }
    lemma |= ineq(m.var(), product.is_neg() ? llc::GE : llc::LE, product);
}
    
/** \brief enforce the inequality |m| >= product |m[i]| .

    /\_i |m[i]| >= |val(m[i])| => |m| >= |product_i val(m[i])|
    <=>
    \/_i |m[i]| < |val(m[i])| or |m| >= |product_i val(m[i])|

    Example:

    x <= -2 & y >= 3 => x*y <= -6
*/
void monotone::monotonicity_lemma_lt(const monic& m) {
    new_lemma lemma(c(), "monotonicity <");
    rational product(1);
    for (lpvar j : m.vars()) {
        auto v = c().val(j);
        lemma |= ineq(j, v.is_neg() ? llc::GT : llc::LT, v);
        product *= v;
    }
    lemma |= ineq(m.var(), product.is_neg() ? llc::LE : llc::GE, product);
}
   

}
