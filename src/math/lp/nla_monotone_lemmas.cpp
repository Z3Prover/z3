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
#include "math/lp/nla_basics_lemmas.h"
#include "math/lp/nla_core.h"
namespace nla {

monotone::monotone(core * c) : common(c, nullptr) {}

    
void monotone::monotonicity_lemma() {
    unsigned shift = random();
    unsigned size = c().m_to_refine.size();
    for(unsigned i = 0; i < size && !done(); i++) { 
        lpvar v = c().m_to_refine[(i + shift) % size];
        monotonicity_lemma(c().emons()[v]);
    }
}


void monotone::negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict) {
    rational av = val(a);
    rational as = rational(nla::rat_sign(av));
    rational bv = val(b);
    rational bs = rational(nla::rat_sign(bv));
    TRACE("nla_solver", tout << "av = " << av << ", bv = " << bv << "\n";);
    SASSERT(as*av <= bs*bv);
    llc mod_s = strict? (llc::LE): (llc::LT);
    mk_ineq(as, a, mod_s); // |a| <= 0 || |a| < 0
    if (a != b) {
        mk_ineq(bs, b, mod_s); // |b| <= 0 || |b| < 0
        mk_ineq(as, a, -bs, b, llc::GT); // negate |aj| <= |bj|
    }
}

void monotone::assert_abs_val_a_le_abs_var_b(
    const monic& a,
    const monic& b,
    bool strict) {
    lpvar aj = var(a);
    lpvar bj = var(b);
    rational av = val(aj);
    rational as = rational(nla::rat_sign(av));
    rational bv = val(bj);
    rational bs = rational(nla::rat_sign(bv));
    //        TRACE("nla_solver", tout << "rmv = " << rmv << ", jv = " << jv << "\n";);
    mk_ineq(as, aj, llc::LT); // |aj| < 0
    mk_ineq(bs, bj, llc::LT); // |bj| < 0
    mk_ineq(as, aj, -bs, bj, strict? llc::LT : llc::LE); // |aj| < |bj|
}

void monotone::negate_abs_a_lt_abs_b(lpvar a, lpvar b) {
    rational av = val(a);
    rational as = rational(nla::rat_sign(av));
    rational bv = val(b);
    rational bs = rational(nla::rat_sign(bv));
    TRACE("nla_solver", tout << "av = " << av << ", bv = " << bv << "\n";);
    SASSERT(as*av < bs*bv);
    mk_ineq(as, a, llc::LT); // |aj| < 0
    mk_ineq(bs, b, llc::LT); // |bj| < 0
    mk_ineq(as, a, -bs, b, llc::GE); // negate  |aj| < |bj|
}
   
void monotone::monotonicity_lemma(monic const& m) {
    SASSERT(!check_monic(m));
    if (c().mon_has_zero(m.vars()))
        return;
    const rational prod_val = abs(c().product_value(m.vars()));
    const rational m_val = abs(val(m));
    if (m_val < prod_val)
        monotonicity_lemma_lt(m, prod_val);
    else if (m_val > prod_val)
        monotonicity_lemma_gt(m, prod_val);
}

void monotone::monotonicity_lemma_gt(const monic& m, const rational& prod_val) {
    TRACE("nla_solver", tout << "prod_val = " << prod_val << "\n";);
    add_empty_lemma();
    for (lpvar j : m.vars()) {
        c().add_abs_bound(j, llc::GT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(m_j, llc::LE, prod_val);
    TRACE("nla_solver", print_lemma(tout););
}
    
/** \brief enforce the inequality |m| >= product |m[i]| .

    /\_i |m[i]| >= |val(m[i])| => |m| >= |product_i val(m[i])|
    <=>
    \/_i |m[i]| < |val(m[i])} or |m| >= |product_i val(m[i])|
*/
void monotone::monotonicity_lemma_lt(const monic& m, const rational& prod_val) {
    add_empty_lemma();
    for (lpvar j : m.vars()) {
        c().add_abs_bound(j, llc::LT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(m_j, llc::GE, prod_val);
    TRACE("nla_solver", print_lemma(tout););
}
   

}
