/*++
  Copyright (c) 2017 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/

#include "math/lp/nla_basics_lemmas.h"
#include "math/lp/nla_core.h"
#include "math/lp/factorization_factory_imp.h"
namespace nla {

typedef lp::lar_term term;

basics::basics(core * c) : common(c) {}

// Monomials m and n vars have the same values, up to "sign"
// Generate a lemma if values of m.var() and n.var() are not the same up to sign
bool basics::basic_sign_lemma_on_two_monics(const monic& m, const monic& n) {
    const rational sign = sign_to_rat(m.rsign() ^ n.rsign());
    if (var_val(m) == var_val(n) * sign)
        return false;
    TRACE("nla_solver", tout << "sign contradiction:\nm = " << pp_mon(c(), m) << "n= " << pp_mon(c(), n) << "sign: " << sign << "\n";);
    generate_sign_lemma(m, n, sign);
    return true;
}

void basics::generate_zero_lemmas(const monic& m) {
    SASSERT(!var_val(m).is_zero() && c().product_value(m).is_zero());
    int sign = nla::rat_sign(var_val(m));
    unsigned_vector fixed_zeros;
    lpvar zero_j = find_best_zero(m, fixed_zeros);
    SASSERT(is_set(zero_j));
    unsigned zero_power = 0;
    for (lpvar j : m.vars()) {
        if (j == zero_j) {
            zero_power++;
            continue;
        }
        get_non_strict_sign(j, sign);
        if (sign == 0)
            break;
    }
    if (sign && is_even(zero_power)) {
        sign = 0;
    }
    TRACE("nla_solver_details", tout << "zero_j = " << zero_j << ", sign = " << sign << "\n";);
    if (sign == 0) { // have to generate a non-convex lemma
        add_trivial_zero_lemma(zero_j, m);
    } else { // here we know the sign of zero_j
        generate_strict_case_zero_lemma(m, zero_j, sign);
    }
    for (lpvar j : fixed_zeros)
        add_fixed_zero_lemma(m, j);
}

bool basics::try_get_non_strict_sign_from_bounds(lpvar j, int& sign) const {
    SASSERT(sign);
    if (c().has_lower_bound(j) && c().get_lower_bound(j) >= rational(0))
        return true;
    if (c().has_upper_bound(j) && c().get_upper_bound(j) <= rational(0)) {
        sign = -sign;
        return true;
    }
    sign = 0;
    return false;
}

void basics::get_non_strict_sign(lpvar j, int& sign) const {
    const rational v = val(j);
    if (v.is_zero()) {
        try_get_non_strict_sign_from_bounds(j, sign);
    } else {
        sign *= nla::rat_sign(v);
    }
}


void basics::basic_sign_lemma_model_based_one_mon(const monic& m, int product_sign) {
    if (product_sign == 0) {
        TRACE("nla_solver_bl", tout << "zero product sign: " << pp_mon(_(), m)<< "\n";);
        generate_zero_lemmas(m);
    } else {
        new_lemma lemma(c(), __FUNCTION__);
        for (lpvar j: m.vars()) {
            negate_strict_sign(lemma, j);
        }
        lemma |= ineq(m.var(), product_sign == 1? llc::GT : llc::LT, 0);
    }
}
    
bool basics::basic_sign_lemma_model_based() {
    unsigned start = c().random();
    unsigned sz = c().m_to_refine.size();
    for (unsigned i = sz; i-- > 0;) {
        monic const& m = c().emons()[c().m_to_refine[(start + i) % sz]];
        int mon_sign = nla::rat_sign(var_val(m));
        int product_sign = c().rat_sign(m);
        if (mon_sign != product_sign) {
            basic_sign_lemma_model_based_one_mon(m, product_sign);
            if (c().done())
                return true;
        }
    }
    return c().m_lemma_vec->size() > 0;
}

    
bool basics::basic_sign_lemma_on_mon(lpvar v, std::unordered_set<unsigned> & explored) {
    if (!try_insert(v, explored)) {
        return false;
    }
    const monic& m_v = c().emons()[v];
    TRACE("nla_solver", tout << "m_v = " << pp_mon_with_vars(c(), m_v););
    CTRACE("nla_solver", !c().emons().is_canonized(m_v),
           c().emons().display(c(), tout);
           c().m_evars.display(tout);
           );
    SASSERT(c().emons().is_canonized(m_v));

    for (auto const& m : c().emons().enum_sign_equiv_monics(v)) {
        TRACE("nla_solver_details", tout << "m = " << pp_mon_with_vars(c(), m););
        SASSERT(m.rvars() == m_v.rvars());
        if (m_v.var() != m.var() && basic_sign_lemma_on_two_monics(m_v, m) && done()) 
            return true;
    }

    TRACE("nla_solver_details", tout << "return false\n";);
    return false;
}

/**
 * \brief <generate lemma by using the fact that -ab = (-a)b) and
 -ab = a(-b)
*/
bool basics::basic_sign_lemma(bool derived) {
    if (!derived)
        return basic_sign_lemma_model_based();

    std::unordered_set<unsigned> explored;
    for (lpvar j : c().m_to_refine) {
        if (basic_sign_lemma_on_mon(j, explored))
            return true;
    }
    return false;
}
// the value of the i-th monic has to be equal to the value of the k-th monic modulo sign
// but it is not the case in the model
void basics::generate_sign_lemma(const monic& m, const monic& n, const rational& sign) {
    new_lemma lemma(c(), "sign lemma");
    TRACE("nla_solver",
          tout << "m = " << pp_mon_with_vars(_(), m);
          tout << "n = " << pp_mon_with_vars(_(), n);
          );
    lemma |= ineq(term(m.var(), -sign, n.var()), llc::EQ, 0);
    lemma &= m;
    lemma &= n;
}
// try to find a variable j such that val(j) = 0
// and the bounds on j contain 0 as an inner point
lpvar basics::find_best_zero(const monic& m, unsigned_vector & fixed_zeros) const {
    lpvar zero_j = null_lpvar;
    for (unsigned j : m.vars()) {
        if (val(j).is_zero()) {
            if (c().var_is_fixed_to_zero(j))
                fixed_zeros.push_back(j);
                
            if (!is_set(zero_j) || c().zero_is_an_inner_point_of_bounds(j))
                zero_j = j;
        }
    }
    return zero_j;    
}

void basics::add_trivial_zero_lemma(lpvar zero_j, const monic& m) {
    new_lemma lemma(c(), "x = 0 => x*y = 0");
    lemma |= ineq(zero_j,  llc::NE, 0);
    lemma |= ineq(m.var(), llc::EQ, 0);
}

void basics::generate_strict_case_zero_lemma(const monic& m, unsigned zero_j, int sign_of_zj) {
    TRACE("nla_solver_bl", tout << "sign_of_zj = " << sign_of_zj << "\n";);
    // we know all the signs
    new_lemma lemma(c(), "strict case 0");
    lemma |= ineq(zero_j, sign_of_zj == 1? llc::GT : llc::LT, 0);
    for (unsigned j : m.vars()) {
        if (j != zero_j) {
            negate_strict_sign(lemma, j);
        }
    }
    negate_strict_sign(lemma, m.var());
}

void basics::add_fixed_zero_lemma(const monic& m, lpvar j) {
    new_lemma lemma(c(), "fixed zero");
    lemma.explain_fixed(j);
    lemma |= ineq(m.var(), llc::EQ, 0);
}

void basics::negate_strict_sign(new_lemma& lemma, lpvar j) {
    TRACE("nla_solver_details", tout << pp_var(c(), j) << " " << val(j).is_zero() << "\n";);
    if (!val(j).is_zero()) {
        int sign = nla::rat_sign(val(j));
        lemma |= ineq(j, (sign == 1? llc::LE : llc::GE), 0);
    } 
    else {  // val(j).is_zero()
        if (c().has_lower_bound(j) && c().get_lower_bound(j) >= rational(0)) {
            lemma.explain_existing_lower_bound(j);
            lemma |= ineq(j, llc::GT, 0);
        } else {
            SASSERT(c().has_upper_bound(j) && c().get_upper_bound(j) <= rational(0));
            lemma.explain_existing_upper_bound(j);
            lemma |= ineq(j, llc::LT, 0);
        }
    }
}

// here we use the fact
// xy = 0 -> x = 0 or y = 0
bool basics::basic_lemma_for_mon_zero(const monic& rm, const factorization& f) {
    // it seems this code is never exercised
    for (auto j : f) {
        if (val(j).is_zero())
            return false;
    }
    TRACE("nla_solver", c().trace_print_monic_and_factorization(rm, f, tout););
    new_lemma lemma(c(), "xy = 0 -> x = 0 or y = 0");
    lemma.explain_fixed(var(rm));
    std::unordered_set<lpvar> processed;
    for (auto j : f) {
        if (try_insert(var(j), processed))
            lemma |= ineq(var(j), llc::EQ, 0);
    }
    lemma &= rm;
    lemma &= f;
    return true;
}

// use basic multiplication properties to create a lemma
bool basics::basic_lemma(bool derived) {
    if (basic_sign_lemma(derived))
        return true;
    if (derived) 
        return false;
    const auto& mon_inds_to_ref = c().m_to_refine;
    TRACE("nla_solver", tout << "mon_inds_to_ref = "; print_vector(mon_inds_to_ref, tout) << "\n";);
    unsigned start = c().random();
    unsigned sz = mon_inds_to_ref.size();
    for (unsigned j = 0; j < sz; ++j) {
        lpvar v = mon_inds_to_ref[(j + start) % mon_inds_to_ref.size()];
        const monic& r = c().emons()[v];
        SASSERT (!c().check_monic(c().emons()[v]));
        basic_lemma_for_mon(r, derived);
    } 
        
    return false;
}
// Use basic multiplication properties to create a lemma
// for the given monic.
// "derived" means derived from constraints - the alternative is model based
void basics::basic_lemma_for_mon(const monic& rm, bool derived) {
    if (derived)
        basic_lemma_for_mon_derived(rm);
    else
        basic_lemma_for_mon_model_based(rm);
}
bool basics::basic_lemma_for_mon_derived(const monic& rm) {
    if (c().var_is_fixed_to_zero(var(rm))) {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;            
            if (basic_lemma_for_mon_zero(rm, factorization))
                return true;
            if (basic_lemma_for_mon_neutral_derived(rm, factorization))
                return true;
        }
    } 
    else {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;
            if (basic_lemma_for_mon_non_zero_derived(rm, factorization))
                return true;
            if (basic_lemma_for_mon_neutral_derived(rm, factorization))
                return true;
        }
    }
    return false;
}

// x = 0 or y = 0 -> xy = 0
bool basics::basic_lemma_for_mon_non_zero_derived(const monic& rm, const factorization& f) {
    TRACE("nla_solver", c().trace_print_monic_and_factorization(rm, f, tout););
    if (!c().var_is_separated_from_zero(var(rm)))
        return false; 
    for (auto fc : f) {
        if (!c().var_is_fixed_to_zero(var(fc))) 
            continue;
        new_lemma lemma(c(), "x = 0 or y = 0 -> xy = 0");
        lemma.explain_fixed(var(fc));
        lemma.explain_var_separated_from_zero(var(rm));
        lemma &= rm;
        lemma &= f;
        return true;
    }
    return false;
}

// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
// it holds for integers, and for reals for a pair of factors
// |x*a| = |x| & x != 0 -> |a| = 1

bool basics::basic_lemma_for_mon_neutral_derived(const monic& rm, const factorization& f) {
    TRACE("nla_solver",  c().trace_print_monic_and_factorization(rm, f, tout););

    lpvar mon_var =  c().emons()[rm.var()].var();
    TRACE("nla_solver",  c().trace_print_monic_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto mv = val(mon_var);
    const auto abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    bool mon_var_is_sep_from_zero =  c().var_is_separated_from_zero(mon_var);
    lpvar u = null_lpvar, v = null_lpvar;
    bool all_int = true;
    for (auto fc : f) {
        lpvar j = var(fc);
        all_int &= c().var_is_int(j);        
        if (j == null_lpvar && abs(val(j)) == abs_mv && 
            c().vars_are_equiv(j, mon_var) &&
            (mon_var_is_sep_from_zero ||  c().var_is_separated_from_zero(j))) 
            u = j;
        else if (abs(val(j)) != rational(1)) 
            v = j;
    }
    if (u == null_lpvar || v == null_lpvar)
        return false;    
    if (!all_int && f.size() > 2)
        return false;

    //    (mon_var != 0 || u != 0) & mon_var = +/- u =>
    //    v = 1 or v = -1
    new_lemma lemma(c(), "|xa| = |x| & x != 0 -> |a| = 1");
    lemma.explain_var_separated_from_zero(mon_var_is_sep_from_zero ? mon_var : u);    
    lemma.explain_equiv(mon_var, u);        
    lemma |= ineq(v, llc::EQ, 1);        
    lemma |= ineq(v, llc::EQ, -1);
    lemma &= rm;
    lemma &= f;
    return true;
}

// x != 0 or y = 0 => |xy| >= |y|
void basics::proportion_lemma_model_based(const monic& rm, const factorization& factorization) {
    if (c().has_real(factorization)) // todo: handle the situaiton when all factors are greater than 1,        
        return;     // or smaller than 1
    rational rmv = abs(var_val(rm));
    if (rmv.is_zero()) {
        SASSERT(c().has_zero_factor(factorization));
        return;
    }
    int factor_index = 0;
    for (factor f : factorization) {
        if (abs(val(f)) > rmv) {
            generate_pl(rm, factorization, factor_index);
            return;
        }
        factor_index++;
    }
}

/**
   m := f_1*...*f_n

   k is the index of such that |m| < |val(m[k]|
  
   If for all 1 <= j <= n, j != k we have f_j != 0 then |m| >= |f_k|

   The lemma looks like
   sign_m*m < 0 or \/_{i != k} f_i = 0 or sign_m*m >= sign_k*f_k
   
*/
void basics::generate_pl_on_mon(const monic& m, unsigned k) {
    SASSERT(!c().has_real(m));
    new_lemma lemma(c(), "generate_pl_on_mon");
    unsigned mon_var = m.var();
    rational mv = val(mon_var);
    SASSERT(abs(mv) < abs(val(m.vars()[k])));
    rational sm = rational(nla::rat_sign(mv));
    lemma |= ineq(term(sm, mon_var), llc::LT, 0);
    for (unsigned fi = 0; fi < m.size(); fi ++) {
        lpvar j = m.vars()[fi];
        if (fi != k) {
            lemma |= ineq(j, llc::EQ, 0);
        } else {
            rational sj = rational(nla::rat_sign(val(j)));
            lemma |= ineq(term(sm, mon_var, -sj, j), llc::GE, 0);
        }
    }
    //    lemma &= m; // no need to "explain" monomial m here
}

/**    
  none of the factors is zero and the product is not zero
   -> |fc[factor_index]| <= |rm|

   m := f1 * .. * f_n
   
   sign_m*m < 0 or f_i = 0 or \/_{j != i} sign_m*m >= sign_j*f_j
*/
void basics::generate_pl(const monic& m, const factorization& fc, int factor_index) {
    SASSERT(!c().has_real(fc));
    TRACE("nla_solver", tout << "factor_index = " << factor_index << ", m = "
          << pp_mon(c(), m);
          tout << ", fc = " << c().pp(fc);
          tout << "orig mon = "; c().print_monic(c().emons()[m.var()], tout););
    if (fc.is_mon()) {
        generate_pl_on_mon(m, factor_index);
        return;
    }
    new_lemma lemma(c(), "generate_pl");
    int fi = 0;
    rational mv = var_val(m);
    rational sm = rational(nla::rat_sign(mv));
    unsigned mon_var = var(m);
    lemma |= ineq(term(sm, mon_var), llc::LT, 0);
    for (factor f : fc) {
        if (fi++ != factor_index) {
            lemma |= ineq(var(f), llc::EQ, 0);
        } else {
            lpvar j = var(f);
            rational jv = val(j);
            rational sj = rational(nla::rat_sign(jv));
            lemma |= ineq(term(sm, mon_var, -sj, j), llc::GE, 0);
        }
    }
    lemma &= fc;
    lemma &= m; 
}

bool basics::is_separated_from_zero(const factorization& f) const {
    for (const factor& fc: f) {
        lpvar j = var(fc);
        if (!(c().var_has_positive_lower_bound(j) || c().var_has_negative_upper_bound(j))) {
            return false;
        }
    }
    return true;
}



// here we use the fact xy = 0 -> x = 0 or y = 0
void basics::basic_lemma_for_mon_zero_model_based(const monic& rm, const factorization& f) {        
    TRACE("nla_solver",  c().trace_print_monic_and_factorization(rm, f, tout););
    SASSERT(var_val(rm).is_zero() && !c().rm_check(rm));
    new_lemma lemma(c(), "xy = 0 -> x = 0 or y = 0");
    if (!is_separated_from_zero(f)) {
        lemma |= ineq(var(rm), llc::NE, 0);
        for (auto j : f) {
            lemma |= ineq(var(j), llc::EQ, 0);
        }
    } else {
        lemma |= ineq(var(rm), llc::NE, 0);
        for (auto j : f) {
            lemma.explain_var_separated_from_zero(var(j));
        }            
    }
    lemma &= f;
}

void basics::basic_lemma_for_mon_model_based(const monic& rm) {
    TRACE("nla_solver_bl", tout << "rm = " << pp_mon(_(), rm) << "\n";);
    if (var_val(rm).is_zero()) {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;
            basic_lemma_for_mon_zero_model_based(rm, factorization);
            basic_lemma_for_mon_neutral_model_based(rm, factorization); // todo - the same call is made in the else branch
        }
    } else {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;
            basic_lemma_for_mon_non_zero_model_based(rm, factorization);
            basic_lemma_for_mon_neutral_model_based(rm, factorization);
            proportion_lemma_model_based(rm, factorization) ;
        }
    }
}


/**
   m = f1 * f2 * .. * fn
   where
   - at most one fi evaluates to something different from +1 or -1
   - sign = f1 * ... f_{i-1} * f_{i+1} * ..
   - sign = +1 or -1
   - add lemma
     - /\_{j != i} f_j = val(f_j) => m = sign * f_i
     or
     - /\_j f_j = val(f_j) => m = sign
*/
bool basics::basic_lemma_for_mon_neutral_from_factors_to_monic_model_based_fm(const monic& m) {
    lpvar not_one; rational sign;
    if (!can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based(m, m, not_one, sign))
        return false;
       
    new_lemma lemma(c(), __FUNCTION__);
    for (auto j : m.vars()) {
        if (not_one != j) 
            lemma |= ineq(j, llc::NE, val(j));
    }

    if (not_one == null_lpvar) 
        lemma |= ineq(m.var(), llc::EQ, sign);
    else 
        lemma |= ineq(term(m.var(), -sign, not_one), llc::EQ, 0);
    return true;
}

// use the fact that
// |uvw| = |u| and uvw != 0 -> |v| = 1 
bool basics::basic_lemma_for_mon_neutral_monic_to_factor_model_based(const monic& rm, const factorization& f) {
    lpvar mon_var = c().emons()[rm.var()].var();
    TRACE("nla_solver_bl", c().trace_print_monic_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto mv = val(mon_var);
    const auto abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    lpvar u = null_lpvar, v = null_lpvar;
    bool all_int = true;
    for (auto fc : f) {
        lpvar j = var(fc);
        all_int &= c().var_is_int(j);        
        if (j == null_lpvar && abs(val(fc)) == abs_mv) 
            u = j;
        else if (abs(val(fc)) != rational(1)) 
            v = j;
    }
    if (u == null_lpvar || v == null_lpvar)
        return false;    
    if (!all_int && f.size() > 2)
        return false;

    // mon_var = 0
    // abs(u) != abs(mon_var)    
    // v = 1
    // v = -1

    new_lemma lemma(c(), __FUNCTION__);
    lemma |= ineq(mon_var, llc::EQ, 0);        
    lemma |= ineq(term(u, rational(val(u) == -val(mon_var) ? 1 : -1), mon_var), llc::NE, 0);
    lemma |= ineq(v, llc::EQ, 1);
    lemma |= ineq(v, llc::EQ, -1);
    lemma &= rm; // NSB review: is this dependency required? - it does because it explains how monomial is equivalent
    // to the rooted monomial
    lemma &= f;

    return true;
}

void basics::basic_lemma_for_mon_neutral_model_based(const monic& rm, const factorization& f) {
    if (f.is_mon()) {
        basic_lemma_for_mon_neutral_monic_to_factor_model_based(rm, f);
        basic_lemma_for_mon_neutral_from_factors_to_monic_model_based_fm(f.mon());
    }
    else {
        basic_lemma_for_mon_neutral_monic_to_factor_model_based(rm, f);
        basic_lemma_for_mon_neutral_from_factors_to_monic_model_based(rm, f);
    }
}
template <typename T>
bool basics::can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based(const monic& m, const T& f, lpvar &not_one, rational& sign) {
    sign = rational(1); 
    //    TRACE("nla_solver_bl", tout << pp_mon_with_vars(_(), m) <<"\nf = " << c().pp(f) << "sign = " << sign << '\n';);
    not_one = null_lpvar;
    for (auto j : f) {
        TRACE("nla_solver_bl", tout << "j = "; c().print_factor_with_vars(j, tout););
        auto v = val(j);

        if (v.is_one()) 
            continue;
            
        if (v.is_minus_one()) {
            sign = -sign;
            continue;
        } 
            
        if (not_one == null_lpvar) {
            not_one = var(j);
            continue;
        }
            
        // if we are here then there are at least two factors with absolute values different from one : cannot create the lemma
        return false;
    }

    if (not_one == null_lpvar && var_val(m) == sign) {
        // we have +-ones only in the factorization
        return false;
    }
    if (not_one != null_lpvar && var_val(m) == val(not_one) * sign) {
        TRACE("nla_solver", tout << "the whole is equal to the factor" << std::endl;);
        return false;        
    }

    return true;
}

/**
 - m := f1*f2*.. 
   - f_i are factors of m
 - at most one variable among f_i evaluates to something else than -1, +1.
   - m = sign * f_i
   - sign = sign of f_1 * .. * f_{i-1} * f_{i+1} ... = +/- 1
 - lemma:
    /\_{j != i} f_j = val(f_j) => m = sign * f_i
    or 
    /\ f_j = val(f_j) => m = sign if all factors evaluate to +/- 1

Note:
   The routine can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based does
   not check the signs of factors. Factors have signs. It works assuming all factors have
   positive signs. 
*/ 
bool basics::basic_lemma_for_mon_neutral_from_factors_to_monic_model_based(const monic& m, const factorization& f) {
    lpvar not_one; rational sign;
    if (!can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based(m, f, not_one, sign))
        return false;
    for (auto j : f) 
        if (j.sign())
            return false;
    TRACE("nla_solver_bl", tout << "not_one = " << not_one << "\n";);
        
    new_lemma lemma(c(), __FUNCTION__);

    for (auto j : f) {
        lpvar var_j = var(j);
        if (not_one == var_j) continue;
        TRACE("nla_solver_bl", tout << "j = "; c().print_factor_with_vars(j, tout););
        lemma |= ineq(var_j, llc::NE, val(var_j));
    }

    if (not_one == null_lpvar) 
        lemma |= ineq(m.var(), llc::EQ, sign);
    else 
        lemma |= ineq(term(m.var(), -sign, not_one), llc::EQ, 0);
    lemma &= m;
    lemma &= f;
    TRACE("nla_solver", tout << "m = " << pp_mon_with_vars(c(), m););
    return true;
}

// x = 0 or y = 0 -> xy = 0
void basics::basic_lemma_for_mon_non_zero_model_based(const monic& rm, const factorization& f) {
    TRACE("nla_solver_bl", c().trace_print_monic_and_factorization(rm, f, tout););
    for (auto j : f) {
        if (val(j).is_zero()) {
            new_lemma lemma(c(), "x = 0 => x*... = 0");
            lemma |= ineq(var(j), llc::NE, 0);
            lemma |= ineq(f.mon().var(), llc::EQ, 0);
            lemma &= f;
            return;
        }
    }
}


}
