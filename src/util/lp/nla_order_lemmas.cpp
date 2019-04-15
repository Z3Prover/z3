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

#include "util/lp/nla_order_lemmas.h"
#include "util/lp/nla_core.h"
#include "util/lp/nla_common.h"
#include "util/lp/factorization_factory_imp.h"

namespace nla {

// a >< b && c > 0  => ac >< bc
// a >< b && c < 0  => ac <> bc
// ac[k] plays the role of c   

bool order::order_lemma_on_ac_and_bc(const rooted_mon& rm_ac,
                                     const factorization& ac_f,
                                     unsigned k,
                                     const rooted_mon& rm_bd) {
    TRACE("nla_solver",   tout << "rm_ac = ";
          c().print_rooted_monomial(rm_ac, tout);
          tout << "\nrm_bd = ";
          c().print_rooted_monomial(rm_bd, tout);
          tout << "\nac_f[k] = ";
          c().print_factor_with_vars(ac_f[k], tout););
    factor b;
    if (!c().divide(rm_bd, ac_f[k], b)){
        return false;
    }

    return order_lemma_on_ac_and_bc_and_factors(rm_ac, ac_f[(k + 1) % 2], ac_f[k], rm_bd, b);
}

bool order::order_lemma_on_ac_explore(const rooted_mon& rm, const factorization& ac, unsigned k) {
    const factor c = ac[k];
    TRACE("nla_solver", tout << "c = "; _().print_factor_with_vars(c, tout); );
    if (c.is_var()) {
        TRACE("nla_solver", tout << "var(c) = " << var(c););
        for (unsigned rm_bc : _().m_rm_table.var_map()[c.index()]) {
            TRACE("nla_solver", );
            if (order_lemma_on_ac_and_bc(rm ,ac, k, _().m_rm_table.rms()[rm_bc])) {
                return true;
            }
        }
    } else {
        for (unsigned rm_bc : _().m_rm_table.proper_multiples()[c.index()]) {
            if (order_lemma_on_ac_and_bc(rm , ac, k, _().m_rm_table.rms()[rm_bc])) {
                return true;
            }
        }
    }
    return false;
}

void order::order_lemma_on_factorization(const rooted_mon& rm, const factorization& ab) {
    const monomial& m = _().m_monomials[rm.orig_index()];
    TRACE("nla_solver", tout << "orig_sign = " << rm.orig_sign() << "\n";);
    rational sign = rm.orig_sign();
    for(factor f: ab)
        sign *= _().canonize_sign(f);
    const rational & fv = vvr(ab[0]) * vvr(ab[1]);
    const rational mv = sign * vvr(m);
    TRACE("nla_solver",
          tout << "ab.size()=" << ab.size() << "\n";
          tout << "we should have sign*vvr(m):" << mv << "=(" << sign << ")*(" << vvr(m) <<") to be equal to " << " vvr(ab[0])*vvr(ab[1]):" << fv << "\n";);
    if (mv == fv)
        return;
    bool gt = mv > fv;
    TRACE("nla_solver_f", tout << "m="; _().print_monomial_with_vars(m, tout); tout << "\nfactorization="; _().print_factorization(ab, tout););
    for (unsigned j = 0, k = 1; j < 2; j++, k--) {
        order_lemma_on_ab(m, sign, var(ab[k]), var(ab[j]), gt);
        explain(ab); explain(m);
        explain(rm);
        TRACE("nla_solver", _().print_lemma(tout););
        order_lemma_on_ac_explore(rm, ab, j);
    }
}
// |c_sign| = 1, and c*c_sign > 0
// ac > bc => ac/|c| > bc/|c| => a*c_sign > b*c_sign
void order::generate_ol(const rooted_mon& ac,                     
                       const factor& a,
                       int c_sign,
                       const factor& c,
                       const rooted_mon& bc,
                       const factor& b,
                       llc ab_cmp) {
    add_empty_lemma();
    rational rc_sign = rational(c_sign);
    mk_ineq(rc_sign * canonize_sign(c), var(c), llc::LE);
    mk_ineq(canonize_sign(ac), var(ac), -canonize_sign(bc), var(bc), ab_cmp);
    mk_ineq(canonize_sign(a)*rc_sign, var(a), - canonize_sign(b)*rc_sign, var(b), negate(ab_cmp));
    explain(ac);
    explain(a);
    explain(bc);
    explain(b);
    explain(c);
    TRACE("nla_solver", _().print_lemma(tout););
}

void order::generate_mon_ol(const monomial& ac,                     
                           lpvar a,
                           const rational& c_sign,
                           lpvar c,
                           const rooted_mon& bd,
                           const factor& b,
                           const rational& d_sign,
                           lpvar d,
                           llc ab_cmp) {
    add_empty_lemma();
    mk_ineq(c_sign, c, llc::LE);
    explain(c); // this explains c == +- d
    negate_var_factor_relation(c_sign, a, d_sign, b);
    mk_ineq(ac.var(), -canonize_sign(bd), var(bd), ab_cmp);
    explain(bd);
    explain(b);
    explain(d);
    TRACE("nla_solver", print_lemma(tout););
}

void order::negate_var_factor_relation(const rational& a_sign, lpvar a, const rational& b_sign, const factor& b) {
    rational b_fs = canonize_sign(b);
    llc cmp = a_sign*vvr(a) < b_sign*vvr(b)? llc::GE : llc::LE;
    mk_ineq(a_sign, a, - b_fs*b_sign, var(b), cmp);
}

void order::order_lemma() {
    TRACE("nla_solver", );
    c().init_rm_to_refine();
    const auto& rm_ref = c().m_rm_table.to_refine();
    unsigned start = random() % rm_ref.size();
    unsigned i = start;
    do {
        const rooted_mon& rm = c().m_rm_table.rms()[rm_ref[i]];
        order_lemma_on_rmonomial(rm);
        if (++i == rm_ref.size()) {
            i = 0;
        }
    } while(i != start && !done());
}

bool order::order_lemma_on_ac_and_bc_and_factors(const rooted_mon& ac,
                                                 const factor& a,
                                                 const factor& c,
                                                 const rooted_mon& bc,
                                                 const factor& b) {
    auto cv = vvr(c); 
    int c_sign = nla::rat_sign(cv);
    SASSERT(c_sign != 0);
    auto av_c_s = vvr(a)*rational(c_sign);
    auto bv_c_s = vvr(b)*rational(c_sign);        
    auto acv = vvr(ac); 
    auto bcv = vvr(bc); 
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
void order::order_lemma_on_ab_gt(const monomial& m, const rational& sign, lpvar a, lpvar b) {
    SASSERT(sign * vvr(m) > vvr(a) * vvr(b));
    add_empty_lemma();
    if (vvr(a).is_pos()) {
        TRACE("nla_solver", tout << "a is pos\n";);
        //negate a > 0
        mk_ineq(a, llc::LE);
        // negate b <= vvr(b)
        mk_ineq(b, llc::GT, vvr(b));
        // ab <= vvr(b)a
        mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);
    } else {
        TRACE("nla_solver", tout << "a is neg\n";);
        SASSERT(vvr(a).is_neg());
        //negate a < 0
        mk_ineq(a, llc::GE);
        // negate b >= vvr(b)
        mk_ineq(b, llc::LT, vvr(b));
        // ab <= vvr(b)a
        mk_ineq(sign, m.var(), -vvr(b), a, llc::LE);
    }
}
// we need to deduce ab >= vvr(b)*a
/**
   \brief Add lemma: 
   a > 0 & b >= value(b) => sign*ab >= value(b)*a if value(a) > 0
   a < 0 & b <= value(b) => sign*ab >= value(b)*a if value(a) < 0
*/
void order::order_lemma_on_ab_lt(const monomial& m, const rational& sign, lpvar a, lpvar b) {
    SASSERT(sign * vvr(m) < vvr(a) * vvr(b));
    add_empty_lemma();
    if (vvr(a).is_pos()) {
        //negate a > 0
        mk_ineq(a, llc::LE);
        // negate b >= vvr(b)
        mk_ineq(b, llc::LT, vvr(b));
        // ab <= vvr(b)a
        mk_ineq(sign, m.var(), -vvr(b), a, llc::GE);
    } else {
        SASSERT(vvr(a).is_neg());
        //negate a < 0
        mk_ineq(a, llc::GE);
        // negate b <= vvr(b)
        mk_ineq(b, llc::GT, vvr(b));
        // ab >= vvr(b)a
        mk_ineq(sign, m.var(), -vvr(b), a, llc::GE);
    }
}

void order::order_lemma_on_ab(const monomial& m, const rational& sign, lpvar a, lpvar b, bool gt) {
    if (gt)
        order_lemma_on_ab_gt(m, sign, a, b);
    else 
        order_lemma_on_ab_lt(m, sign, a, b);
}
// a > b && c > 0 => ac > bc
void order::order_lemma_on_rmonomial(const rooted_mon& rm) {
    TRACE("nla_solver_details",
          tout << "rm = "; print_product(rm, tout);
          tout << ", orig = "; print_monomial(c().m_monomials[rm.orig_index()], tout);
          );
    for (auto ac : factorization_factory_imp(rm, c())) {
        if (ac.size() != 2)
            continue;
        if (ac.is_mon())
            order_lemma_on_binomial(*ac.mon());
        else
            order_lemma_on_factorization(rm, ac);
        if (done())
            break;
    }
}
void order::order_lemma_on_binomial_k(const monomial& m, lpvar k, bool gt) {
    SASSERT(gt == (vvr(m) > vvr(m[0]) * vvr(m[1])));
    unsigned p = (k + 1) % 2;
    order_lemma_on_binomial_sign(m, m[k], m[p], gt? 1: -1);
}
// sign it the sign of vvr(m) - vvr(m[0]) * vvr(m[1])
// m = xy
// and val(m) != val(x)*val(y)
// y > 0 and x = a, then xy >= ay
void order::order_lemma_on_binomial_sign(const monomial& ac, lpvar x, lpvar y, int sign) {
    SASSERT(!_().mon_has_zero(ac));
    int sy = rat_sign(vvr(y));
    add_empty_lemma();
    mk_ineq(y, sy == 1? llc::LE : llc::GE); // negate sy
    mk_ineq(x, sy*sign == 1? llc::GT:llc::LT , vvr(x)); // assert x <= vvr(x) if x > 0
    mk_ineq(ac.var(), - vvr(x), y, sign == 1?llc::LE:llc::GE);
    TRACE("nla_solver", print_lemma(tout););
}
void order::order_lemma_on_factor_binomial_rm(const monomial& ac, unsigned k, const rooted_mon& rm_bd) {
    factor d(_().m_evars.find(ac[k]).var(), factor_type::VAR);
    factor b;
    if (!_().divide(rm_bd, d, b))
        return;
    order_lemma_on_binomial_ac_bd(ac, k, rm_bd, b, d.index());
}

void order::order_lemma_on_binomial_ac_bd(const monomial& ac, unsigned k, const rooted_mon& bd, const factor& b, lpvar d) {
    TRACE("nla_solver",  print_monomial(ac, tout << "ac=");
          print_rooted_monomial(bd, tout << "\nrm=");
          print_factor(b, tout << ", b="); print_var(d, tout << ", d=") << "\n";);
    int p = (k + 1) % 2;
    lpvar a = ac[p];
    lpvar c = ac[k];
    SASSERT(_().m_evars.find(c).var() == d);
    rational acv = vvr(ac);
    rational av = vvr(a);
    rational c_sign = rrat_sign(vvr(c));
    rational d_sign = rrat_sign(vvr(d));
    rational bdv = vvr(bd);
    rational bv = vvr(b);
    auto av_c_s = av*c_sign; auto bv_d_s = bv*d_sign;

    // suppose ac >= bd, then ac/|c| >= bd/|d|.
    // Notice that ac/|c| = a*c_sign , and bd/|d| = b*d_sign
    if (acv >= bdv && av_c_s < bv_d_s)
        generate_mon_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::LT);
    else if (acv <= bdv && av_c_s > bv_d_s)
        generate_mon_ol(ac, a, c_sign, c, bd, b, d_sign, d, llc::GT);
        
}

void order::order_lemma_on_factor_binomial_explore(const monomial& m, unsigned k) {
    SASSERT(m.size() == 2);
    lpvar c = m[k];
    lpvar d = _().m_evars.find(c).var();
    auto it = _().m_rm_table.var_map().find(d);
    SASSERT(it != _().m_rm_table.var_map().end());
    for (unsigned bd_i : it->second) {
        order_lemma_on_factor_binomial_rm(m, k, _().m_rm_table.rms()[bd_i]);
        if (done())
            break;
    }        
}

void order::order_lemma_on_binomial(const monomial& ac) {
    TRACE("nla_solver", print_monomial(ac, tout););
    SASSERT(!check_monomial(ac) && ac.size() == 2);
    const rational & mult_val = vvr(ac[0]) * vvr(ac[1]);
    const rational acv = vvr(ac);
    bool gt = acv > mult_val;
    for (unsigned k = 0; k < 2; k++) {
        order_lemma_on_binomial_k(ac, k, gt);
        order_lemma_on_factor_binomial_explore(ac, k);
    }
}
} // end of namespace nla
