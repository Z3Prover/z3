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
#include "util/lp/nla_basics_lemmas.h"
#include "util/lp/nla_core.h"
#include "util/lp/factorization_factory_imp.h"
namespace nla {

basics::basics(core * c) : common(c) {}

// Monomials m and n vars have the same values, up to "sign"
// Generate a lemma if values of m.var() and n.var() are not the same up to sign
bool basics::basic_sign_lemma_on_two_monomials(const monomial& m, const monomial& n, const rational& sign) {
    if (vvr(m) == vvr(n) * sign)
        return false;
    TRACE("nla_solver", tout << "sign contradiction:\nm = " << m << "n= " << n << "sign: " << sign << "\n";);
    generate_sign_lemma(m, n, sign);
    return true;
}

void basics::generate_zero_lemmas(const monomial& m) {
    SASSERT(!vvr(m).is_zero() && c().product_value(m).is_zero());
    int sign = nla::rat_sign(vvr(m));
    unsigned_vector fixed_zeros;
    lpvar zero_j = find_best_zero(m, fixed_zeros);
    SASSERT(is_set(zero_j));
    unsigned zero_power = 0;
    for (lpvar j : m){
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
        add_trival_zero_lemma(zero_j, m);
    } else { 
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
    const rational & v = vvr(j);
    if (v.is_zero()) {
        try_get_non_strict_sign_from_bounds(j, sign);
    } else {
        sign *= nla::rat_sign(v);
    }
}


void basics::basic_sign_lemma_model_based_one_mon(const monomial& m, int product_sign) {
    if (product_sign == 0) {
        TRACE("nla_solver_bl", tout << "zero product sign\n";);
        generate_zero_lemmas(m);
    } else {
        add_empty_lemma();
        for(lpvar j: m) {
            negate_strict_sign(j);
        }
        c().mk_ineq(m.var(), product_sign == 1? llc::GT : llc::LT);
        TRACE("nla_solver", c().print_lemma(tout); tout << "\n";);
    }
}
    
bool basics::basic_sign_lemma_model_based() {
    unsigned start = c().random();
    unsigned sz = c().m_to_refine.size();
    for (unsigned i = sz; i-- > 0; ) {
        monomial const& m = c().m_emons[c().m_to_refine[(start + i) % sz]];
        int mon_sign = nla::rat_sign(vvr(m));
        int product_sign = c().rat_sign(m);
        if (mon_sign != product_sign) {
            basic_sign_lemma_model_based_one_mon(m, product_sign);
            if (c().done())
                return true;
        }
    }
    return c().m_lemma_vec->size() > 0;
}

    
bool basics::basic_sign_lemma_on_mon(lpvar v, std::unordered_set<unsigned> & explored){
    if (!try_insert(v, explored)) {
        return false;
    }

    const monomial& m_v = c().m_emons[v];
    smon const& sv_v = c().m_emons.canonical[v];
    TRACE("nla_solver_details", tout << "mon = " << pp_mon(c(), m_v););

    for (auto const& m_w : c().m_emons.enum_sign_equiv_monomials(v)) {
        smon const& sv_w = c().m_emons.canonical[m_w];
        if (m_v.var() != m_w.var() && basic_sign_lemma_on_two_monomials(m_v, m_w, sv_v.rsign() * sv_w.rsign()) && done()) 
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
    for (lpvar i : c().m_to_refine){
        if (basic_sign_lemma_on_mon(i, explored))
            return true;
    }
    return false;
}
// the value of the i-th monomial has to be equal to the value of the k-th monomial modulo sign
// but it is not the case in the model
void basics::generate_sign_lemma(const monomial& m, const monomial& n, const rational& sign) {
    add_empty_lemma();
    TRACE("nla_solver",
          tout << "m = "; c().print_monomial_with_vars(m, tout);
          tout << "n = "; c().print_monomial_with_vars(n, tout);
          );
    c().mk_ineq(m.var(), -sign, n.var(), llc::EQ);
    explain(m);
    explain(n);        
    TRACE("nla_solver", c().print_lemma(tout););
}
// try to find a variable j such that vvr(j) = 0
// and the bounds on j contain 0 as an inner point
lpvar basics::find_best_zero(const monomial& m, unsigned_vector & fixed_zeros) const {
    lpvar zero_j = -1;
    for (unsigned j : m){
        if (vvr(j).is_zero()){
            if (c().var_is_fixed_to_zero(j))
                fixed_zeros.push_back(j);
                
            if (!is_set(zero_j) || c().zero_is_an_inner_point_of_bounds(j))
                zero_j = j;
        }
    }
    return zero_j;    
}
void basics::add_trival_zero_lemma(lpvar zero_j, const monomial& m) {
    add_empty_lemma();
    c().mk_ineq(zero_j, llc::NE);
    c().mk_ineq(m.var(), llc::EQ);
    TRACE("nla_solver", c().print_lemma(tout););            
}
void basics::generate_strict_case_zero_lemma(const monomial& m, unsigned zero_j, int sign_of_zj) {
    TRACE("nla_solver_bl", tout << "sign_of_zj = " << sign_of_zj << "\n";);
    // we know all the signs
    add_empty_lemma();
    c().mk_ineq(zero_j, (sign_of_zj == 1? llc::GT : llc::LT));
    for (unsigned j : m){
        if (j != zero_j) {
            negate_strict_sign(j);
        }
    }
    negate_strict_sign(m.var());
    TRACE("nla_solver", c().print_lemma(tout););
}
void basics::add_fixed_zero_lemma(const monomial& m, lpvar j) {
    add_empty_lemma();
    c().explain_fixed_var(j);
    c().mk_ineq(m.var(), llc::EQ);
    TRACE("nla_solver", c().print_lemma(tout););
}
void basics::negate_strict_sign(lpvar j) {
    TRACE("nla_solver_details", c().print_var(j, tout););
    if (!vvr(j).is_zero()) {
        int sign = nla::rat_sign(vvr(j));
        c().mk_ineq(j, (sign == 1? llc::LE : llc::GE));
    } else {   // vvr(j).is_zero()
        if (c().has_lower_bound(j) && c().get_lower_bound(j) >= rational(0)) {
            c().explain_existing_lower_bound(j);
            c().mk_ineq(j, llc::GT);
        } else {
            SASSERT(c().has_upper_bound(j) && c().get_upper_bound(j) <= rational(0));
            c().explain_existing_upper_bound(j);
            c().mk_ineq(j, llc::LT);
        }
    }
}

// here we use the fact
// xy = 0 -> x = 0 or y = 0
bool basics::basic_lemma_for_mon_zero(const smon& rm, const factorization& f) {
    NOT_IMPLEMENTED_YET();
    return true;
#if 0
    TRACE("nla_solver", c().trace_print_monomial_and_factorization(rm, f, tout););
    add_empty_lemma();
    c().explain_fixed_var(var(rm));
    std::unordered_set<lpvar> processed;
    for (auto j : f) {
        if (try_insert(var(j), processed))
            c().mk_ineq(var(j), llc::EQ);
    }
    explain(rm);
    TRACE("nla_solver", c().print_lemma(tout););
    return true;
#endif
}
// use basic multiplication properties to create a lemma
bool basics::basic_lemma(bool derived) {
    if (basic_sign_lemma(derived))
        return true;
    if (derived)
        return false;
    const auto& rm_ref = c().m_to_refine;
    TRACE("nla_solver", tout << "rm_ref = "; print_vector(rm_ref, tout););
    unsigned start = c().random();
    unsigned sz = rm_ref.size();
    for (unsigned j = 0; j < sz; ++j) {
        lpvar v = rm_ref[(j + start) % rm_ref.size()];
        const smon& r = c().m_emons.canonical[v];
        SASSERT (!c().check_monomial(c().m_emons[v]));
        basic_lemma_for_mon(r, derived);
    } 
        
    return false;
}
// Use basic multiplication properties to create a lemma
// for the given monomial.
// "derived" means derived from constraints - the alternative is model based
void basics::basic_lemma_for_mon(const smon& rm, bool derived) {
    if (derived)
        basic_lemma_for_mon_derived(rm);
    else
        basic_lemma_for_mon_model_based(rm);
}
bool basics::basic_lemma_for_mon_derived(const smon& rm) {
    if (c().var_is_fixed_to_zero(var(rm))) {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;
            if (basic_lemma_for_mon_zero(rm, factorization) ||
                basic_lemma_for_mon_neutral_derived(rm, factorization)) {
                explain(factorization);
                return true;
            }
        }
    } else {
        for (auto factorization : factorization_factory_imp(rm, c())) {
            if (factorization.is_empty())
                continue;
            if (basic_lemma_for_mon_non_zero_derived(rm, factorization) ||
                basic_lemma_for_mon_neutral_derived(rm, factorization) ||
                proportion_lemma_derived(rm, factorization)) {
                explain(factorization);
                return true;
            }
        }
    }
    return false;
}
// x = 0 or y = 0 -> xy = 0
bool basics::basic_lemma_for_mon_non_zero_derived(const smon& rm, const factorization& f) {
    TRACE("nla_solver", c().trace_print_monomial_and_factorization(rm, f, tout););
    if (! c().var_is_separated_from_zero(var(rm)))
        return false; 
    int zero_j = -1;
    for (auto j : f) {
        if ( c().var_is_fixed_to_zero(var(j))) {
            zero_j = var(j);
            break;
        }
    }

    if (zero_j == -1) {
        return false;
    } 
    add_empty_lemma();
    c().explain_fixed_var(zero_j);
    c().explain_var_separated_from_zero(var(rm));
    explain(rm);
    TRACE("nla_solver",  c().print_lemma(tout););
    return true;
}
// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
bool basics::basic_lemma_for_mon_neutral_monomial_to_factor_derived(const smon& rm, const factorization& f) {
    TRACE("nla_solver",  c().trace_print_monomial_and_factorization(rm, f, tout););

    lpvar mon_var =  c().m_emons[rm.var()].var();
    TRACE("nla_solver",  c().trace_print_monomial_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto & mv = vvr(mon_var);
    const auto  abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    bool mon_var_is_sep_from_zero =  c().var_is_separated_from_zero(mon_var);
    lpvar jl = -1;
    for (auto fc : f ) {
        lpvar j = var(fc);
        if (abs(vvr(j)) == abs_mv &&  c().vars_are_equiv(j, mon_var) &&
            (mon_var_is_sep_from_zero ||  c().var_is_separated_from_zero(j))) {
            jl = j;
            break;
        }
    }
    if (jl == static_cast<lpvar>(-1))
        return false;
        
    lpvar not_one_j = -1;
    for (auto j : f ) {
        if (var(j) == jl) {
            continue;
        }
        if (abs(vvr(j)) != rational(1)) {
            not_one_j = var(j);
            break;
        }
    }

    if (not_one_j == static_cast<lpvar>(-1)) {
        return false;
    } 

    add_empty_lemma();
    // mon_var = 0
    if (mon_var_is_sep_from_zero)
         c().explain_var_separated_from_zero(mon_var);
    else
         c().explain_var_separated_from_zero(jl);

     c().explain_equiv_vars(mon_var, jl);
        
    // not_one_j = 1
    c().mk_ineq(not_one_j, llc::EQ,  rational(1));   
        
    // not_one_j = -1
    c().mk_ineq(not_one_j, llc::EQ, -rational(1));
    explain(rm);
    TRACE("nla_solver",  c().print_lemma(tout); );
    return true;
}
// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool basics::basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(const smon& rm, const factorization& f) {
    return false;
    rational sign = c().m_emons.orig_sign(rm);
    lpvar not_one = -1;

    TRACE("nla_solver", tout << "f = ";  c().print_factorization(f, tout););
    for (auto j : f){
        TRACE("nla_solver", tout << "j = ";  c().print_factor_with_vars(j, tout););
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }

        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 

        if (not_one == static_cast<lpvar>(-1)) {
            not_one = var(j);
            continue;
        }

        // if we are here then there are at least two factors with values different from one and minus one: cannot create the lemma
        return false;
    }

    add_empty_lemma();
    explain(rm);

    for (auto j : f){
        lpvar var_j = var(j);
        if (not_one == var_j) continue;
        c().mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) :  c().canonize_sign(j) * vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        c().mk_ineq( c().m_emons[rm.var()].var(), llc::EQ, sign);
    } else {
        c().mk_ineq( c().m_emons[rm.var()].var(), -sign, not_one, llc::EQ);
    }
    TRACE("nla_solver",
          tout << "rm = " << rm;
          c().print_lemma(tout););
    return true;
}

bool basics::basic_lemma_for_mon_neutral_derived(const smon& rm, const factorization& factorization) {
    return
        basic_lemma_for_mon_neutral_monomial_to_factor_derived(rm, factorization) || 
        basic_lemma_for_mon_neutral_from_factors_to_monomial_derived(rm, factorization);
    return false;
}

// x != 0 or y = 0 => |xy| >= |y|
void basics::proportion_lemma_model_based(const smon& rm, const factorization& factorization) {
    rational rmv = abs(vvr(rm));
    if (rmv.is_zero()) {
        SASSERT(c().has_zero_factor(factorization));
        return;
    }
    int factor_index = 0;
    for (factor f : factorization) {
        if (abs(vvr(f)) > rmv) {
            generate_pl(rm, factorization, factor_index);
            return;
        }
        factor_index++;
    }
}
// x != 0 or y = 0 => |xy| >= |y|
bool basics::proportion_lemma_derived(const smon& rm, const factorization& factorization) {
    return false;
    rational rmv = abs(vvr(rm));
    if (rmv.is_zero()) {
        SASSERT(c().has_zero_factor(factorization));
        return false;
    }
    int factor_index = 0;
    for (factor f : factorization) {
        if (abs(vvr(f)) > rmv) {
            generate_pl(rm, factorization, factor_index);
            return true;
        }
        factor_index++;
    }
    return false;
}
// if there are no zero factors then |m| >= |m[factor_index]|
void basics::generate_pl_on_mon(const monomial& m, unsigned factor_index) {
    add_empty_lemma();
    unsigned mon_var = m.var();
    rational mv = vvr(mon_var);
    rational sm = rational(nla::rat_sign(mv));
    c().mk_ineq(sm, mon_var, llc::LT);
    for (unsigned fi = 0; fi < m.size(); fi ++) {
        lpvar j = m[fi];
        if (fi != factor_index) {
            c().mk_ineq(j, llc::EQ);
        } else {
            rational jv = vvr(j);
            rational sj = rational(nla::rat_sign(jv));
            SASSERT(sm*mv < sj*jv);
            c().mk_ineq(sj, j, llc::LT);
            c().mk_ineq(sm, mon_var, -sj, j, llc::GE );
        }
    }
    TRACE("nla_solver", c().print_lemma(tout); );
}
    
// none of the factors is zero and the product is not zero
// -> |fc[factor_index]| <= |rm|
void basics::generate_pl(const smon& rm, const factorization& fc, int factor_index) {
    TRACE("nla_solver", tout << "factor_index = " << factor_index << ", rm = ";
          tout << rm;
          tout << "fc = "; c().print_factorization(fc, tout);
          tout << "orig mon = "; c().print_monomial(c().m_emons[rm.var()], tout););
    if (fc.is_mon()) {
        generate_pl_on_mon(*fc.mon(), factor_index);
        return;
    }
    add_empty_lemma();
    int fi = 0;
    rational rmv = vvr(rm);
    rational sm = rational(nla::rat_sign(rmv));
    unsigned mon_var = var(rm);
    c().mk_ineq(sm, mon_var, llc::LT);
    for (factor f : fc) {
        if (fi++ != factor_index) {
            c().mk_ineq(var(f), llc::EQ);
        } else {
            lpvar j = var(f);
            rational jv = vvr(j);
            rational sj = rational(nla::rat_sign(jv));
            SASSERT(sm*rmv < sj*jv);
            c().mk_ineq(sj, j, llc::LT);
            c().mk_ineq(sm, mon_var, -sj, j, llc::GE );
        }
    }
    if (!fc.is_mon()) {
        explain(fc);
        explain(rm);
    }
    TRACE("nla_solver", c().print_lemma(tout); );
}   
// here we use the fact xy = 0 -> x = 0 or y = 0
void basics::basic_lemma_for_mon_zero_model_based(const smon& rm, const factorization& f) {        
    TRACE("nla_solver",  c().trace_print_monomial_and_factorization(rm, f, tout););
    SASSERT(vvr(rm).is_zero()&& ! c().rm_check(rm));
    add_empty_lemma();
    int sign =  c().get_derived_sign(rm, f);
    if (sign == 0) {
        c().mk_ineq(var(rm), llc::NE);        
        for (auto j : f) {
            c().mk_ineq(var(j), llc::EQ);
        }
    } else {
        c().mk_ineq(var(rm), llc::NE);        
        for (auto j : f) {
            c().explain_separation_from_zero(var(j));
        }            
    }
    explain(rm);
    explain(f);
    TRACE("nla_solver", c().print_lemma(tout););
}

void basics::basic_lemma_for_mon_model_based(const smon& rm) {
    TRACE("nla_solver_bl", tout << "rm = " << rm;);
    if (vvr(rm).is_zero()) {
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

// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
bool basics::basic_lemma_for_mon_neutral_monomial_to_factor_model_based_fm(const monomial& m) {
    TRACE("nla_solver_bl", c().print_monomial(m, tout););

    lpvar mon_var = m.var();
    const auto & mv = vvr(mon_var);
    const auto  abs_mv = abs(mv);
    if (abs_mv == rational::zero()) {
        return false;
    }
    lpvar jl = -1;
    for (auto j : m ) {
        if (abs(vvr(j)) == abs_mv) {
            jl = j;
            break;
        }
    }
    if (jl == static_cast<lpvar>(-1))
        return false;
    lpvar not_one_j = -1;
    for (auto j : m ) {
        if (j == jl) {
            continue;
        }
        if (abs(vvr(j)) != rational(1)) {
            not_one_j = j;
            break;
        }
    }

    if (not_one_j == static_cast<lpvar>(-1)) {
        return false;
    } 

    add_empty_lemma();
    // mon_var = 0
    c().mk_ineq(mon_var, llc::EQ);
        
    // negate abs(jl) == abs()
    if (vvr(jl) == - vvr(mon_var))
        c().mk_ineq(jl, mon_var, llc::NE, c().current_lemma());   
    else  // jl == mon_var
        c().mk_ineq(jl, -rational(1), mon_var, llc::NE);   

    // not_one_j = 1
    c().mk_ineq(not_one_j, llc::EQ,  rational(1));   
        
    // not_one_j = -1
    c().mk_ineq(not_one_j, llc::EQ, -rational(1));
    TRACE("nla_solver", c().print_lemma(tout); );
    return true;
}
// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool basics::basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based_fm(const monomial& m) {
    lpvar not_one = -1;
    rational sign(1);
    TRACE("nla_solver_bl", tout << "m = "; c().print_monomial(m, tout););
    for (auto j : m){
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }
        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 
        if (not_one == static_cast<lpvar>(-1)) {
            not_one = j;
            continue;
        }
        // if we are here then there are at least two factors with values different from one and minus one: cannot create the lemma
        return false;
    }

    if (not_one + 1) {  // we found the only not_one
        if (vvr(m) == vvr(not_one) * sign) {
            TRACE("nla_solver", tout << "the whole equal to the factor" << std::endl;);
            return false;
        }
    }
        
    add_empty_lemma();
    for (auto j : m){
        if (not_one == j) continue;
        c().mk_ineq(j, llc::NE, vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        c().mk_ineq(m.var(), llc::EQ, sign);
    } else {
        c().mk_ineq(m.var(), -sign, not_one, llc::EQ);
    }
    TRACE("nla_solver",  c().print_lemma(tout););
    return true;
}

// use the fact that
// |xabc| = |x| and x != 0 -> |a| = |b| = |c| = 1 
bool basics::basic_lemma_for_mon_neutral_monomial_to_factor_model_based(const smon& rm, const factorization& f) {
    TRACE("nla_solver_bl", c().trace_print_monomial_and_factorization(rm, f, tout););

    lpvar mon_var = c().m_emons[rm.var()].var();
    TRACE("nla_solver_bl", c().trace_print_monomial_and_factorization(rm, f, tout); tout << "\nmon_var = " << mon_var << "\n";);
        
    const auto & mv = vvr(mon_var);
    const auto  abs_mv = abs(mv);
        
    if (abs_mv == rational::zero()) {
        return false;
    }
    lpvar jl = -1;
    for (auto j : f ) {
        if (abs(vvr(j)) == abs_mv) {
            jl = var(j);
            break;
        }
    }
    if (jl == static_cast<lpvar>(-1))
        return false;
    lpvar not_one_j = -1;
    for (auto j : f ) {
        if (var(j) == jl) {
            continue;
        }
        if (abs(vvr(j)) != rational(1)) {
            not_one_j = var(j);
            break;
        }
    }

    if (not_one_j == static_cast<lpvar>(-1)) {
        return false;
    } 

    add_empty_lemma();
    // mon_var = 0
    c().mk_ineq(mon_var, llc::EQ);
        
    // negate abs(jl) == abs()
    if (vvr(jl) == - vvr(mon_var))
        c().mk_ineq(jl, mon_var, llc::NE, c().current_lemma());   
    else  // jl == mon_var
        c().mk_ineq(jl, -rational(1), mon_var, llc::NE);   

    // not_one_j = 1
    c().mk_ineq(not_one_j, llc::EQ,  rational(1));   
        
    // not_one_j = -1
    c().mk_ineq(not_one_j, llc::EQ, -rational(1));
    explain(rm);
    explain(f);

    TRACE("nla_solver", c().print_lemma(tout); );
    return true;
}

void basics::basic_lemma_for_mon_neutral_model_based(const smon& rm, const factorization& f) {
    if (f.is_mon()) {
        basic_lemma_for_mon_neutral_monomial_to_factor_model_based_fm(*f.mon());
        basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based_fm(*f.mon());
    }
    else {
        basic_lemma_for_mon_neutral_monomial_to_factor_model_based(rm, f);
        basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(rm, f);
    }
}
// use the fact
// 1 * 1 ... * 1 * x * 1 ... * 1 = x
bool basics::basic_lemma_for_mon_neutral_from_factors_to_monomial_model_based(const smon& rm, const factorization& f) {
    rational sign = c().m_emons.orig_sign(rm);
    TRACE("nla_solver_bl", tout << "f = "; c().print_factorization(f, tout); tout << ", sign = " << sign << '\n'; );
    lpvar not_one = -1;
    for (auto j : f){
        TRACE("nla_solver_bl", tout << "j = "; c().print_factor_with_vars(j, tout););
        auto v = vvr(j);
        if (v == rational(1)) {
            continue;
        }
            
        if (v == -rational(1)) { 
            sign = - sign;
            continue;
        } 
            
        if (not_one == static_cast<lpvar>(-1)) {
            not_one = var(j);
            continue;
        }
            
        // if we are here then there are at least two factors with absolute values different from one : cannot create the lemma
        return false;
    }

    if (not_one + 1) {
        // we found the only not_one
        if (vvr(rm) == vvr(not_one) * sign) {
            TRACE("nla_solver", tout << "the whole equal to the factor" << std::endl;);
            return false;
        }
    } else {
        // we have +-ones only in the factorization
        if (vvr(rm) == sign) {
            return false;
        }
    }

    TRACE("nla_solver_bl", tout << "not_one = " << not_one << "\n";);
        
    add_empty_lemma();

    for (auto j : f){
        lpvar var_j = var(j);
        if (not_one == var_j) continue;
        c().mk_ineq(var_j, llc::NE, j.is_var()? vvr(j) : c().canonize_sign(j) * vvr(j));   
    }

    if (not_one == static_cast<lpvar>(-1)) {
        c().mk_ineq(rm.var(), llc::EQ, sign);
    } else {
        c().mk_ineq(rm.var(), -sign, not_one, llc::EQ);
    }
    explain(rm);
    explain(f);
    TRACE("nla_solver",
          c().print_lemma(tout);
          tout << "rm = " << rm;
          );
    return true;
}


void basics::basic_lemma_for_mon_non_zero_model_based_mf(const factorization& f) {
    TRACE("nla_solver_bl", c().print_factorization(f, tout););
    int zero_j = -1;
    for (auto j : f) {
        if (vvr(j).is_zero()) {
            zero_j = var(j);
            break;
        }
    }

    if (zero_j == -1) { return; } 
    add_empty_lemma();
    c().mk_ineq(zero_j, llc::NE);
    c().mk_ineq(f.mon()->var(), llc::EQ);
    TRACE("nla_solver", c().print_lemma(tout););
}

// x = 0 or y = 0 -> xy = 0
void basics::basic_lemma_for_mon_non_zero_model_based(const smon& rm, const factorization& f) {
    TRACE("nla_solver_bl", c().trace_print_monomial_and_factorization(rm, f, tout););
    if (f.is_mon())
        basic_lemma_for_mon_non_zero_model_based_mf(f);
    else
        basic_lemma_for_mon_non_zero_model_based_mf(f);
}


}
