/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)
  --*/

#include "math/lp/nla_order_lemmas.h"
#include "math/lp/nla_core.h"
#include "math/lp/nla_common.h"
#include "math/lp/factorization_factory_imp.h"

namespace nla {

typedef lp::lar_term term;

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
    const rational mult_val = mul_val(ac);
    const rational acv = var_val(ac);
    bool gt = acv > mult_val;
    bool k = false;
    do {
        order_lemma_on_binomial_sign(ac, ac.vars()[k], ac.vars()[!k], gt? 1: -1);
        order_lemma_on_factor_binomial_explore(ac, k);
        k = !k; 
    } 
    while (k);
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
    if (!c().var_is_int(x) && val(x).is_big())
        return;
    SASSERT(!_().mon_has_zero(xy.vars()));
    int sy = rat_sign(val(y));
    new_lemma lemma(c(), __FUNCTION__);
    lemma |= ineq(y,                                   sy == 1      ? llc::LE : llc::GE, 0); // negate sy
    lemma |= ineq(x,                                   sy*sign == 1 ? llc::GT : llc::LT , val(x)); 
    lemma |= ineq(term(xy.var(), - val(x), y), sign == 1    ? llc::LE : llc::GE, 0);
}

// We look for monics e = m.rvars()[k]*d and see if we can create an order lemma for m and  e
void order::order_lemma_on_factor_binomial_explore(const monic& ac, bool k) {
    TRACE("nla_solver", tout << "ac = " <<  pp_mon_with_vars(c(), ac););
    SASSERT(ac.size() == 2);    
    lpvar c = ac.vars()[k];
    
    for (monic const& bd : _().emons().get_products_of(c)) {
        if (bd.var() == ac.var()) 
            continue;
        TRACE("nla_solver", tout << "bd = " << pp_mon_with_vars(_(), bd););
        order_lemma_on_factor_binomial_rm(ac, k, bd);
        if (done()) 
            break;
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
    rational acv = var_val(ac);
    rational av = val(a);
    rational c_sign = rrat_sign(val(c));
    rational d_sign = rrat_sign(val(d));
    rational bdv = var_val(bd);
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
    SASSERT(ab_cmp == llc::LT || ab_cmp == llc::GT);
    SASSERT(ab_cmp != llc::LT || (var_val(ac) >= var_val(bd) && val(a)*c_sign < val(b)*d_sign));
    SASSERT(ab_cmp != llc::GT || (var_val(ac) <= var_val(bd) && val(a)*c_sign > val(b)*d_sign));
    
    new_lemma lemma(_(), __FUNCTION__);
    lemma |= ineq(term(c_sign, c), llc::LE, 0);
    lemma &= c; // this explains c == +- d
    lemma |= ineq(term(c_sign, a, -d_sign * b.rat_sign(), b.var()), negate(ab_cmp), 0);
    lemma |= ineq(term(ac.var(), rational(-1), var(bd)), ab_cmp, 0);
    lemma &= bd;
    lemma &= b;
    lemma &= d;
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


// Here m = ab, that is ab is binary factorization of m.
// We try to find a monic n = cd, such that |b| = |d| 
// and get lemma m R n & |b| = |d| => ab/|b| R cd /|d|, where R is a relation
void order::order_lemma_on_factorization(const monic& m, const factorization& ab) {
    bool sign = false;
    for (factor f: ab)  
        sign ^= f.sign();
    const rational rsign = sign_to_rat(sign);
    const rational fv = val(var(ab[0])) * val(var(ab[1]));
    const rational mv = rsign * var_val(m);
    TRACE("nla_solver",
          tout << "ab.size()=" << ab.size() << "\n";
          tout << "we should have mv =" << mv << " = " << fv << " = fv\n";
          tout << "m = "; _().print_monic_with_vars(m, tout); tout << "\nab ="; _().print_factorization(ab, tout););

    if (mv != fv && !c().has_real(m)) {            
        bool gt = mv > fv;
        for (unsigned j = 0, k = 1; j < 2; j++, k--) {
            new_lemma lemma(_(), __FUNCTION__);
            order_lemma_on_ab(lemma, m, rsign, var(ab[k]), var(ab[j]), gt);
            lemma &= ab;
            lemma &= m;
        }
    }
    for (unsigned j = 0, k = 1; j < 2; j++, k--) {
        order_lemma_on_ac_explore(m, ab, j == 1);
    }
}

void order::order_lemma_on_ac_explore(const monic& rm, const factorization& ac, bool k) {
    const factor c = ac[k];
    TRACE("nla_solver", tout << "c = "; _().print_factor_with_vars(c, tout); );
    if (c.is_var()) {
        TRACE("nla_solver", tout << "var(c) = " << var(c););
        for (monic const& bc : _().emons().get_use_list(c.var())) {
            if (order_lemma_on_ac_and_bc(rm, ac, k, bc)) 
                return;
        }
    } 
    else {
        for (monic const& bc : _().emons().get_products_of(c.var())) {
            if (order_lemma_on_ac_and_bc(rm, ac, k, bc)) 
                return;
        }
    }
}

void order::generate_ol_eq(const monic& ac,                     
                        const factor& a,
                        const factor& c,
                        const monic& bc,
                        const factor& b) {
    
    new_lemma lemma(_(), __FUNCTION__);
    IF_VERBOSE(100, 
               verbose_stream() 
               << var_val(ac) << "(" << mul_val(ac) << "): " << ac 
               << " " << var_val(bc) << "(" << mul_val(bc) << "): " << bc << "\n"
               << " a " << "*v" << var(a) << " " << val(a) << "\n"
               << " b " <<  "*v" << var(b) << " " << val(b) << "\n"
               << " c " <<  "*v" << var(c) << " " << val(c) << "\n");
    // ac == bc
    lemma |= ineq(c.var(), llc::EQ, 0); // c is not equal to zero
    lemma |= ineq(term(ac.var(), -rational(1), bc.var()), llc::NE, 0);
    lemma |= ineq(term(a.rat_sign(), a.var(), -b.rat_sign(), b.var()), llc::EQ, 0);
    lemma &= ac;
    lemma &= a;
    lemma &= bc;
    lemma &= b;
    lemma &= c;
}

void order::generate_ol(const monic& ac,                     
                        const factor& a,
                        const factor& c,
                        const monic& bc,
                        const factor& b) {
    
    new_lemma lemma(_(), __FUNCTION__);
    TRACE("nla_solver", _().trace_print_ol(ac, a, c, bc, b, tout););        
    IF_VERBOSE(10, verbose_stream() << var_val(ac) << "(" << mul_val(ac) << "): " << ac 
               << " " << var_val(bc) << "(" << mul_val(bc) << "): " << bc << "\n"
               << " a " << "*v" << var(a) << " " << val(a) << "\n"
               << " b " << "*v" << var(b) << " " << val(b) << "\n"
               << " c " << "*v" << var(c) << " " << val(c) << "\n");
    // c > 0 and ac >= bc => a >= b
    // c > 0 and ac <= bc => a <= b
    // c < 0 and ac >= bc => a <= b
    // c < 0 and ac <= bc => a >= b

    
    lemma |= ineq(c.var(), val(c.var()).is_neg() ? llc::GE : llc::LE, 0);
    lemma |= ineq(term(rational(1), ac.var(), -rational(1), bc.var()), var_val(ac) < var_val(bc) ? llc::GT : llc::LT, 0);
    // The value of factor k is val(k) = k.rat_sign()*val(k.var()).
    // That is why we need to use the factor signs of a and b in the term,
    // but the constraint of the lemma is defined by val(a) and val(b).
    lemma |= ineq(term(a.rat_sign(), a.var(),  -b.rat_sign(), b.var()),  val(a)  < val(b)  ? llc::GE : llc::LE, 0);

    lemma &= ac;
    lemma &= a;
    lemma &= bc;
    lemma &= b;
    lemma &= c;
}

// We have ac = a*c and bc = b*c.
// Suppose ac >= bc, then ac/|c| >= bc/|c|
// Notice that ac/|c| = a*rat_sign(val(c)|, and similar fo bc/|c|.
// 
bool order::order_lemma_on_ac_and_bc_and_factors(const monic& ac,
                                                 const factor& a,
                                                 const factor& c,
                                                 const monic& bc,
                                                 const factor& b) {
    SASSERT(!val(c).is_zero());
    rational c_sign = rational(nla::rat_sign(val(c)));
    auto av_c_s = val(a) * c_sign;
    auto bv_c_s = val(b) * c_sign;      
    if ((var_val(ac) > var_val(bc) && av_c_s < bv_c_s) ||
        (var_val(ac) < var_val(bc) && av_c_s > bv_c_s)) {
        generate_ol(ac, a, c, bc, b);
        return true;
    } 
    else if ((var_val(ac) == var_val(bc)) && (av_c_s != bv_c_s)) {
        generate_ol_eq(ac, a, c, bc, b);
        return true;
    }
    return false;
}
/*
   given: sign * m = ab
   lemma b != val(b) || sign*m <= a*val(b)
*/
void order::order_lemma_on_ab_gt(new_lemma& lemma, const monic& m, const rational& sign, lpvar a, lpvar b) {
    SASSERT(sign * var_val(m) > val(a) * val(b));
    // negate b == val(b)
    lemma |= ineq(b, llc::NE, val(b));
    // ab <= val(b)a
    lemma |= ineq(term(sign, m.var(), -val(b), a), llc::LE, 0);
}
/*
   given: sign * m = ab
   lemma b != val(b) || sign*m >= a*val(b)
*/
void order::order_lemma_on_ab_lt(new_lemma& lemma, const monic& m, const rational& sign, lpvar a, lpvar b) {
    TRACE("nla_solver", tout << "sign = " << sign << ", m = "; c().print_monic(m, tout) << ", a = "; c().print_var(a, tout) <<
          ", b = "; c().print_var(b, tout) << "\n";);
    SASSERT(sign * var_val(m) < val(a) * val(b));
    // negate b == val(b)
    lemma |= ineq(b, llc::NE, val(b));
    // ab >= val(b)a
    lemma |= ineq(term(sign, m.var(), -val(b), a), llc::GE, 0);
}

void order::order_lemma_on_ab(new_lemma& lemma, const monic& m, const rational& sign, lpvar a, lpvar b, bool gt) {
    if (gt)
        order_lemma_on_ab_gt(lemma, m, sign, a, b);
    else 
        order_lemma_on_ab_lt(lemma, m, sign, a, b);
}

}
