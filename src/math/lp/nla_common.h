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
#include "util/rational.h"
#include "math/lp/nla_defs.h"
#include "math/lp/lar_term.h"
#include "math/lp/monic.h"
#include "math/lp/emonics.h"
#include "math/lp/factorization.h"
namespace nla {


inline llc negate(llc cmp) {
    switch(cmp) {
    case llc::LE: return llc::GT;
    case llc::LT: return llc::GE;
    case llc::GE: return llc::LT;
    case llc::GT: return llc::LE;
    case llc::EQ: return llc::NE;
    case llc::NE: return llc::EQ;
    default: SASSERT(false);
    };
    return cmp; // not reachable
}

class core;
struct common {
    core* m_core;
    common(core* c): m_core(c) {}
    core& c() { return *m_core; }
    const core& c() const { return *m_core; }
    core& _() { return *m_core; }
    const core& _() const { return *m_core; }

    template <typename T> rational val(T const& t) const;
    rational val(lpvar) const;
    rational rval(const monic&) const;
    template <typename T> lpvar var(T const& t) const;
    bool done() const;
    template <typename T> void explain(const T&);
    void explain(lpvar);
    void add_empty_lemma();
    template <typename T> bool canonize_sign(const T&) const;
    void mk_ineq(lp::lar_term& t, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, const rational& b, lpvar k, llc cmp);

    void mk_ineq(const rational& a, lpvar j, const rational& b, lpvar k, llc cmp);
    void mk_ineq(bool a, lpvar j, bool b, lpvar k, llc cmp);

    void mk_ineq(const rational& a ,lpvar j, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, lpvar k, llc cmp, const rational& rs);

    void mk_ineq(lpvar j, llc cmp, const rational& rs);

    void mk_ineq(const rational& a, lpvar j, llc cmp, const rational& rs);
    void mk_ineq(const rational& a, lpvar j, llc cmp);

    void mk_ineq(lpvar j, llc cmp);

    std::ostream& print_lemma(std::ostream&) const;

    template <typename T>
    std::ostream& print_product(const T & m, std::ostream& out) const;

    std::ostream& print_factor(const factor &, std::ostream& out) const;
    std::ostream& print_var(lpvar, std::ostream& out) const;
    
    std::ostream& print_monic(const monic & m, std::ostream& out) const;
    std::ostream& print_rooted_monic(const monic &, std::ostream& out) const;
    std::ostream& print_rooted_monic_with_vars(const monic&, std::ostream& out) const;
    bool check_monic(const monic&) const;
    unsigned random();
};
}
