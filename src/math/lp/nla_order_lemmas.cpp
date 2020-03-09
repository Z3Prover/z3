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

#include "math/lp/nla_order_lemmas.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_common.h"
#include "math/lp/factorization_factory_imp.h"

namespace nla {

// The order lemma is
// a > b && c > 0 => ac > bc
void order::order_lemma() {
    TRACE("nla_solver", );
    if (!c().m_nla_settings.run_order()) {
        TRACE("nla_solver", tout << "not generating order lemmas\n";);
        return;
    }
    
    const auto& to_ref = c().m_to_refine;
    unsigned r = random();
    unsigned sz = to_ref.size();
    for (unsigned i = 0; i < sz && !done(); ++i) {
        lpvar j = to_ref[(i + r) % sz];
        order_lemma_on_monic(c().emons()[j]);
    }
}

// The order lemma is
// a > b && c > 0 => ac > bc
// Consider here some binary factorizations of m=ac and
// try create order lemmas with either factor playing the role of c.
void order::order_lemma_on_monic(const monic& m) {
    TRACE("nla_solver_details",
          tout << "m = " << pp_mon(c(), m););

    for (auto ac : factorization_factory_imp(m, _())) {
        if (ac.size() != 2)
            continue;
        if (ac.is_mon())
            order_lemma_on_binomial(ac.mon());
        else
            order_lemma_on_factorization(m, ac);
        if (done())
            break;
    }
}
// Here ac is a monic of size 2
// Trying to get an order lemma is
// a > b && c > 0 => ac > bc,
// with either variable of ac playing the role of c
void order::order_lemma_on_binomial(const monic& ac) {
    TRACE("nla_solver", tout << pp_mon_with_vars(c(), ac););
    SASSERT(!check_monic(ac) && ac.size() == 2);
    const rational mult_val = val(ac.vars()[0]) * val(ac.vars()[1]);
    const rational acv = val(ac);
    bool gt = acv > mult_val;
    bool k = false;
    do {
        order_lemma_on_binomial_sign(ac, ac.vars()[k], ac.vars()[!k], gt? 1: -1);
        order_lemma_on_factor_binomial_explore(ac, k);
        k = !k; 
    } while (k);
}


/**
\brief
 sign = the sign of val(xy) - val(x) * val(y) != 0
 y <= 0 or x < a or xy >= ay
 y <= 0 or x > a or xy <= ay
 y >= 0 or x < a or xy <= ay
 y >= 0 or x > a or xy >= ay
  
*/
void order::order_lemma_on_binomial_sign(const monic& xy, lpvar x, lpvar y, int sign) {
    SASSERT(!_().mon_has_zero(xy.vars()));
    int sy = rat_sign(val(y));
    add_empty_lemma();
    mk_ineq(y,                     sy == 1      ? llc::LE : llc::GE); // negate sy
    mk_ineq(x,                     sy*sign == 1 ? llc::GT : llc::LT , val(x)); 
    mk_ineq(xy.var(), - val(x), y, sign == 1    ? llc::LE : llc::GE);
    TRACE("nla_solver", print_lemma(tout););
}

// We look for monics e = m.rvars()[k]*d and see if we can create an order lemma for m and  e
void order::order_lemma_on_factor_binomial_explore(const monic& ac, bool k) {
    TRACE("nla_solver", tout << "ac = " <<  pp_mon_with_vars(c(), ac););
    SASSERT(ac.size() == 2);    
    lpvar c = ac.vars()[k];
    
    for (monic const& bd : _().emons().get_products_of(c)) {
        if (bd.var() == ac.var()) continue;
        TRACE("nla_solver", tout << "bd = " << pp_mon_with_vars(_(), bd););
        order_lemma_on_factor_binomial_rm(ac, k, bd);
        if (done()) {
            break;
        }
    }
}

// ac is a binomial
// create order lemma on monics bd where d is equivalent to ac[k]
void order::order_lemma_on_factor_binomial_rm(const monic& ac, bool k, const monic& bd) {
    TRACE("nla_solver",
          tout << "ac=" << pp_mon_with_vars(_(), ac) << "\n";
          tout << "k=" << k << "\n";
          tout << "bd=" << pp_mon_with_vars(_(), bd) << "\n";
          );
    factor d(_().m_evars.find(ac.vars()[k]).var(), factor_type::VAR);
    factor b(false);
    if (c().divide(bd, d, b)) {
        order_lemma_on_binomial_ac_bd(ac, k, bd, b, d.var());
    }
}

//  ac >= bd && |c| = |d| => ac/|c| >= bd/|d|
void order::order_lemma_on_binomial_ac_bd(const monic& ac, bool k, const monic& bd, const factor& b, lpvar d) {
    lpvar a = ac.vars()[!k];
    lpvar c = ac.vars()[k];
    TRACE("nla_solver",  
          tout << "ac = " << pp_mon(_(), ac) << "a = " << pp_var(_(), a) << "c = " << pp_var(_(), c) << "\nbd = " << pp_mon(_(), bd) << "b = " << pp_fac(_(), b) << "d = " << pp_var(_(), d) << "\n";
          );
    SASSERT(_().m_evars.find(c).var() == d);
    rational acv = val(ac);
    rational av = val(a);
    rational c_sign = rrat_sign(val(c));
    rational d_sign = rrat_sign(val(d));
    rational bdv = val(bd);
    rational bv = val(b);
    // Notice that ac/|c| = a*c_sign , and bd/|d| = b*d_sign
    auto av_c_s = av*c_sign; auto bv_d_s = bv*d_sign;
    TRACE("nla_solver",  
          tout << "acv = " << acv << ", av = " << av << ", c_sign = " << c_sign << ", d_sign = " << d_sign << ", bdv = " << bdv <<
          "\nbv = " << bv << ", av_c_s = " << av_c_s << ", bv_d_s = " << bv_d_s << "\n";);
   
    if (acv >= bdv && av_c_s < bv_d_s)
        generate_mon_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::LT);
    else if (acv <= bdv && av_c_s > bv_d_s)
        generate_mon_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::GT);
        
}

// |c_sign| = 1, and c*c_sign > 0
// |d_sign| = 1, and d*d_sign > 0
// c and d are equivalent |c| == |d|
// ac > bd => ac/|c| > bd/|d| => a*c_sign > b*d_sign
// but the last inequality does not hold
void order::generate_mon_ol(const monic& ac,                     
                           lpvar a,
                           const rational& c_sign,
                           lpvar c,
                           const monic& bd,
                           const factor& b,
                           const rational& d_sign,
                           lpvar d,
                           llc ab_cmp) {
    SASSERT(
        (ab_cmp == llc::LT || ab_cmp == llc::GT) &&
        (
            (ab_cmp != llc::LT ||
             (val(ac) >= val(bd) && val(a)*c_sign < val(b)*d_sign))
            ||
            (ab_cmp != llc::GT ||
             (val(ac) <= val(bd) && val(a)*c_sign > val(b)*d_sign))
         )
            );
    
    add_empty_lemma();
    mk_ineq(c_sign, c, llc::LE);
    explain(c); // this explains c == +- d
    mk_ineq(c_sign, a, -d_sign * b.rat_sign(), b.var(), negate(ab_cmp));
    mk_ineq(ac.var(), rational(-1), var(bd), ab_cmp);
    explain(bd);
    explain(b);
    explain(d);
    TRACE("nla_solver", print_lemma(tout););
}


// a > b  && c > 0 => ac > bc
// a >< b && c > 0 => ac >< bc
// a >< b && c < 0 => ac <> bc
// ac[k] plays the role of c   

bool order::order_lemma_on_ac_and_bc(const monic& rm_ac,
                                     const factorization& ac_f,
                                     bool k,
                                     const monic& rm_bd) {
    TRACE("nla_solver", 
          tout << "rm_ac = " << pp_mon_with_vars(_(), rm_ac) << "\n";
          tout << "rm_bd = " << pp_mon_with_vars(_(), rm_bd) << "\n";
          tout << "ac_f[k] = ";
          c().print_factor_with_vars(ac_f[k], tout););
    factor b(false);
    return 
        c().divide(rm_bd, ac_f[k], b) && 
        order_lemma_on_ac_and_bc_and_factors(rm_ac, ac_f[!k], ac_f[k], rm_bd, b);
}


// Here ab is a binary factorization of m.
// We try to find a monic n = cd, such that |b| = |d| 
// and get a lemma m R n & |b| = |d| => ab/|b| R cd /|d|, where R is a relation
void order::order_lemma_on_factorization(const monic& m, const factorization& ab) {
    bool sign = m.rsign();
    for (factor f: ab)
        sign ^= _().canonize_sign(f);
    const rational fv = val(ab[0]) * val(ab[1]);
    const rational mv = sign_to_rat(sign) * val(m);
    TRACE("nla_solver",
          tout << "ab.size()=" << ab.size() << "\n";
          tout << "we should have sign*val(m):" << mv << "=(" << sign << ")*(" << val(m) <<") to be equal to " << " val(ab[0])*val(ab[1]):" << fv << "\n";);
    if (mv == fv)
        return;
    bool gt = mv > fv;
    TRACE("nla_solver", tout << "m="; _().print_monic_with_vars(m, tout); tout << "\nfactorization="; _().print_factorization(ab, tout););
    for (unsigned j = 0, k = 1; j < 2; j++, k--) {
        order_lemma_on_ab(m, sign_to_rat(sign), var(ab[k]), var(ab[j]), gt);
        explain(ab); explain(m);
        TRACE("nla_solver", _().print_lemma(tout););
        order_lemma_on_ac_explore(m, ab, j == 1);
    }
}

bool order::order_lemma_on_ac_explore(const monic& rm, const factorization& ac, bool k) {
    const factor c = ac[k];
    TRACE("nla_solver", tout << "c = "; _().print_factor_with_vars(c, tout); );
    if (c.is_var()) {
        TRACE("nla_solver", tout << "var(c) = " << var(c););
        for (monic const& bc : _().emons().get_use_list(c.var())) {
            if (order_lemma_on_ac_and_bc(rm ,ac, k, bc)) {
                return true;
            }
        }
    } 
    else {
        for (monic const& bc : _().emons().get_products_of(c.var())) {
            if (order_lemma_on_ac_and_bc(rm , ac, k, bc)) {
                return true;
            }
        }
    }
    return false;
}

// |c_sign| = 1, and c*c_sign > 0
// ac > bc => ac/|c| > bc/|c| => a*c_sign > b*c_sign
void order::generate_ol(const monic& ac,                     
                       const factor& a,
                       int c_sign,
                       const factor& c,
                       const monic& bc,
                       const factor& b,
                       llc ab_cmp) {
    add_empty_lemma();
    rational rc_sign = rational(c_sign);
    mk_ineq(rc_sign * sign_to_rat(canonize_sign(c)), var(c), llc::LE);
    mk_ineq(canonize_sign(ac), var(ac), !canonize_sign(bc), var(bc), ab_cmp);
    mk_ineq(sign_to_rat(canonize_sign(a))*rc_sign, var(a), - sign_to_rat(canonize_sign(b))*rc_sign, var(b), negate(ab_cmp));
    explain(ac);
    explain(a);
    explain(bc);
    explain(b);
    explain(c);
    TRACE("nla_solver", _().print_lemma(tout););
}

bool order::order_lemma_on_ac_and_bc_and_factors(const monic& ac,
                                                 const factor& a,
                                                 const factor& c,
                                                 const monic& bc,
                                                 const factor& b) {
    auto cv = val(c); 
    int c_sign = nla::rat_sign(cv);
    SASSERT(c_sign != 0);
    auto av_c_s = val(a)*rational(c_sign);
    auto bv_c_s = val(b)*rational(c_sign);        
    auto acv = val(ac); 
    auto bcv = val(bc); 
    TRACE("nla_solver", _().trace_print_ol(ac, a, c, bc, b, tout););
    // Suppose ac >= bc, then ac/|c| >= bc/|c|.
    // Notice that ac/|c| = a*c_sign , and bc/|c| = b*c_sign, which are correspondingly av_c_s and bv_c_s
    if (acv >= bcv && av_c_s < bv_c_s) {
        generate_ol(ac, a, c_sign, c, bc, b, llc::LT);
        return true;
    } else if (acv <= bcv && av_c_s > bv_c_s) {
        generate_ol(ac, a, c_sign, c, bc, b, llc::GT);
        return true;
    }
    return false;
}
/**
   \brief Add lemma: 
   a > 0 & b <= value(b) => sign*ab <= value(b)*a  if value(a) > 0
   a < 0 & b >= value(b) => sign*ab <= value(b)*a  if value(a) < 0
*/
void order::order_lemma_on_ab_gt(const monic& m, const rational& sign, lpvar a, lpvar b) {
    SASSERT(sign * val(m) > val(a) * val(b));
    add_empty_lemma();
    if (val(a).is_pos()) {
        TRACE("nla_solver", tout << "a is pos\n";);
        //negate a > 0
        mk_ineq(a, llc::LE);
        // negate b <= val(b)
        mk_ineq(b, llc::GT, val(b));
        // ab <= val(b)a
        mk_ineq(sign, m.var(), -val(b), a, llc::LE);
    } else {
        TRACE("nla_solver", tout << "a is neg\n";);
        SASSERT(val(a).is_neg());
        //negate a < 0
        mk_ineq(a, llc::GE);
        // negate b >= val(b)
        mk_ineq(b, llc::LT, val(b));
        // ab <= val(b)a
        mk_ineq(sign, m.var(), -val(b), a, llc::LE);
    }
}
// we need to deduce ab >= val(b)*a
/**
   \brief Add lemma: 
   a > 0 & b >= value(b) => sign*ab >= value(b)*a if value(a) > 0
   a < 0 & b <= value(b) => sign*ab >= value(b)*a if value(a) < 0
*/
void order::order_lemma_on_ab_lt(const monic& m, const rational& sign, lpvar a, lpvar b) {
    SASSERT(sign * val(m) < val(a) * val(b));
    add_empty_lemma();
    if (val(a).is_pos()) {
        //negate a > 0
        mk_ineq(a, llc::LE);
        // negate b >= val(b)
        mk_ineq(b, llc::LT, val(b));
        // ab <= val(b)a
        mk_ineq(sign, m.var(), -val(b), a, llc::GE);
    } else {
        SASSERT(val(a).is_neg());
        //negate a < 0
        mk_ineq(a, llc::GE);
        // negate b <= val(b)
        mk_ineq(b, llc::GT, val(b));
        // ab >= val(b)a
        mk_ineq(sign, m.var(), -val(b), a, llc::GE);
    }
}

void order::order_lemma_on_ab(const monic& m, const rational& sign, lpvar a, lpvar b, bool gt) {
    if (gt)
        order_lemma_on_ab_gt(m, sign, a, b);
    else 
        order_lemma_on_ab_lt(m, sign, a, b);
}

}
