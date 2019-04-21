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
// #include "util/lp/factorization_factory_imp.h"
namespace nla {

monotone::monotone(core * c) : common(c) {}

    
void monotone::monotonicity_lemma() {
    unsigned shift = random();
    unsigned size = c().m_to_refine.size();
    for(unsigned i = 0; i < size && !done(); i++) { 
        lpvar v = c().m_to_refine[(i + shift) % size];
        monotonicity_lemma(c().m_emons[v]);
    }
}

void monotone::print_monotone_array(const monotone_array_t& lex_sorted,
                                    std::ostream& out) const {
    out << "Monotone array :\n";
    for (const auto & t : lex_sorted ){
        out << "(";
        print_vector(t.first, out);
        out << "), rm[" << t.second << "]" << std::endl;
    }
    out <<  "}";
}

bool monotone::monotonicity_lemma_on_lex_sorted_rm_upper(const monotone_array_t& lex_sorted, unsigned i, const smon& rm) {
    const rational v = abs(vvr(rm));
    const auto& key = lex_sorted[i].first;
    TRACE("nla_solver", tout << "rm = " << rm << ", i = " << i << std::endl;);
    for (unsigned k = i + 1; k < lex_sorted.size(); k++) {
        const auto& p = lex_sorted[k];
        const smon& rmk = c().m_emons.canonical[p.second];
        const rational vk = abs(vvr(rmk));
        TRACE("nla_solver", tout << "rmk = " << rmk << "\n";
              tout << "vk = " << vk << std::endl;);
        if (vk > v) continue;
        unsigned strict;
        if (uniform_le(key, p.first, strict)) {
            if (static_cast<int>(strict) != -1 && !has_zero(key)) {
                generate_monl_strict(rm, rmk, strict);
                return true;
            } 
            else if (vk < v) {
                generate_monl(rm, rmk);
                return true;
            }
        }
            
    }
    return false;
}

bool monotone::monotonicity_lemma_on_lex_sorted_rm_lower(const monotone_array_t& lex_sorted, unsigned i, const smon& rm) {
    const rational v = abs(vvr(rm));
    const auto& key = lex_sorted[i].first;
    TRACE("nla_solver", tout << "rm = " << rm << "i = " << i << std::endl;);
        
    for (unsigned k = i; k-- > 0;) {
        const auto& p = lex_sorted[k];
        const smon& rmk = c().m_emons.canonical[p.second];
        const rational vk = abs(vvr(rmk));
        TRACE("nla_solver", tout << "rmk = " << rmk << "\n";
              tout << "vk = " << vk << std::endl;);
        if (vk < v) continue;
        unsigned strict;
        if (uniform_le(p.first, key, strict)) {
            TRACE("nla_solver", tout << "strict = " << strict << std::endl;);
            if (static_cast<int>(strict) != -1) {
                generate_monl_strict(rmk, rm, strict);
                return true;
            } else {
                SASSERT(key == p.first); 
                if (vk < v) {
                    generate_monl(rmk, rm);
                    return true;
                }
            }
        }
            
    }
    return false;
}

bool monotone::monotonicity_lemma_on_lex_sorted_rm(const monotone_array_t& lex_sorted, unsigned i, const smon& rm) {
    return monotonicity_lemma_on_lex_sorted_rm_upper(lex_sorted, i, rm)
        || monotonicity_lemma_on_lex_sorted_rm_lower(lex_sorted, i, rm);
}
bool monotone::monotonicity_lemma_on_lex_sorted(const monotone_array_t& lex_sorted) {
    for (unsigned i = 0; i < lex_sorted.size(); i++) {
        unsigned rmi = lex_sorted[i].second;
        const smon& rm = c().m_emons.canonical[rmi];
        TRACE("nla_solver", tout << rm << "\n, rm_check = " << c().rm_check(rm); tout << std::endl;); 
        if ((!c().rm_check(rm)) && monotonicity_lemma_on_lex_sorted_rm(lex_sorted, i, rm))
            return true;
    }
    return false;
}

vector<std::pair<rational, lpvar>> monotone::get_sorted_key_with_vars(const smon& a) const {
    vector<std::pair<rational, lpvar>> r;
    for (lpvar j : a.rvars()) {
        r.push_back(std::make_pair(abs(vvr(j)), j));
    }
    std::sort(r.begin(), r.end(), [](const std::pair<rational, lpvar>& a,
                                     const std::pair<rational, lpvar>& b) {
                                      return
                                          a.first < b.first ||
                                                    (a.first == b.first &&
                                                     a.second < b.second);
                                  });
    return r;
} 

void monotone::negate_abs_a_le_abs_b(lpvar a, lpvar b, bool strict) {
    rational av = vvr(a);
    rational as = rational(nla::rat_sign(av));
    rational bv = vvr(b);
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

// strict version
void monotone::generate_monl_strict(const smon& a,
                                    const smon& b,
                                    unsigned strict) {
    add_empty_lemma();
    auto akey = get_sorted_key_with_vars(a);
    auto bkey = get_sorted_key_with_vars(b);
    SASSERT(akey.size() == bkey.size());
    for (unsigned i = 0; i < akey.size(); i++) {
        if (i != strict) {
            negate_abs_a_le_abs_b(akey[i].second, bkey[i].second, true);
        } else {
            mk_ineq(b[i], llc::EQ);
            negate_abs_a_lt_abs_b(akey[i].second, bkey[i].second);
        }
    }
    assert_abs_val_a_le_abs_var_b(a, b, true);
    explain(a);
    explain(b);
    TRACE("nla_solver", print_lemma(tout););
}

void monotone::assert_abs_val_a_le_abs_var_b(
    const smon& a,
    const smon& b,
    bool strict) {
    lpvar aj = var(a);
    lpvar bj = var(b);
    rational av = vvr(aj);
    rational as = rational(nla::rat_sign(av));
    rational bv = vvr(bj);
    rational bs = rational(nla::rat_sign(bv));
    //        TRACE("nla_solver", tout << "rmv = " << rmv << ", jv = " << jv << "\n";);
    mk_ineq(as, aj, llc::LT); // |aj| < 0
    mk_ineq(bs, bj, llc::LT); // |bj| < 0
    mk_ineq(as, aj, -bs, bj, strict? llc::LT : llc::LE); // |aj| < |bj|
}

void monotone::negate_abs_a_lt_abs_b(lpvar a, lpvar b) {
    rational av = vvr(a);
    rational as = rational(nla::rat_sign(av));
    rational bv = vvr(b);
    rational bs = rational(nla::rat_sign(bv));
    TRACE("nla_solver", tout << "av = " << av << ", bv = " << bv << "\n";);
    SASSERT(as*av < bs*bv);
    mk_ineq(as, a, llc::LT); // |aj| < 0
    mk_ineq(bs, b, llc::LT); // |bj| < 0
    mk_ineq(as, a, -bs, b, llc::GE); // negate  |aj| < |bj|
}


// not a strict version
void monotone::generate_monl(const smon& a,
                             const smon& b) {
    TRACE("nla_solver", 
          tout << "a = " << a << "\n:";
          tout << "b = " << b << "\n:";);
    add_empty_lemma();
    auto akey = get_sorted_key_with_vars(a);
    auto bkey = get_sorted_key_with_vars(b);
    SASSERT(akey.size() == bkey.size());
    for (unsigned i = 0; i < akey.size(); i++) {
        negate_abs_a_le_abs_b(akey[i].second, bkey[i].second, false);
    }
    assert_abs_val_a_le_abs_var_b(a, b, false);
    explain(a);
    explain(b);
    TRACE("nla_solver", print_lemma(tout););
}

std::vector<rational> monotone::get_sorted_key(const smon& rm) const {
    std::vector<rational> r;
    for (unsigned j : rm.rvars()) {
        r.push_back(abs(vvr(j)));
    }
    std::sort(r.begin(), r.end());
    return r;
}
    
bool monotone::monotonicity_lemma_on_rms_of_same_arity(const unsigned_vector& rms) { 
    monotone_array_t lex_sorted;
    for (unsigned i : rms) {
        lex_sorted.push_back(std::make_pair(get_sorted_key(c().m_emons.canonical[i]), i));
    }
    std::sort(lex_sorted.begin(), lex_sorted.end(),
              [](const std::pair<std::vector<rational>, unsigned> &a,
                 const std::pair<std::vector<rational>, unsigned> &b) {
                  return a.first < b.first;
              });
    TRACE("nla_solver", print_monotone_array(lex_sorted, tout););
    return monotonicity_lemma_on_lex_sorted(lex_sorted);
}

void monotone::monotonicity_lemma(monomial const& m) {
    SASSERT(!check_monomial(m));
    if (c().mon_has_zero(m))
        return;
    const rational prod_val = abs(c().product_value(m));
    const rational m_val = abs(vvr(m));
    if (m_val < prod_val)
        monotonicity_lemma_lt(m, prod_val);
    else if (m_val > prod_val)
        monotonicity_lemma_gt(m, prod_val);
}

void monotone::monotonicity_lemma_gt(const monomial& m, const rational& prod_val) {
    add_empty_lemma();
    for (lpvar j : m) {
        c().add_abs_bound(j, llc::GT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(m_j, llc::LE, prod_val);
    TRACE("nla_solver", print_lemma(tout););
}
    
/** \brief enforce the inequality |m| >= product |m[i]| .

    /\_i |m[i]| >= |vvr(m[i])| => |m| >= |product_i vvr(m[i])|
    <=>
    \/_i |m[i]| < |vvr(m[i])} or |m| >= |product_i vvr(m[i])|
*/
void monotone::monotonicity_lemma_lt(const monomial& m, const rational& prod_val) {
    add_empty_lemma();
    for (lpvar j : m) {
        c().add_abs_bound(j, llc::LT);
    }
    lpvar m_j = m.var();
    c().add_abs_bound(m_j, llc::GE, prod_val);
    TRACE("nla_solver", print_lemma(tout););
}
   

}
