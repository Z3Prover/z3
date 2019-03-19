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
#include "util/vector.h"
#include "util/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"
#include "util/lp/lar_solver.h"
#include "util/lp/monomial.h"

namespace nla {
struct ineq {
    lp::lconstraint_kind m_cmp;
    lp::lar_term         m_term;
    rational             m_rs;
    ineq(lp::lconstraint_kind cmp, const lp::lar_term& term, const rational& rs) : m_cmp(cmp), m_term(term), m_rs(rs) {}
    bool operator==(const ineq& a) const {
        return m_cmp == a.m_cmp && m_term == a.m_term && m_rs == a.m_rs;
    }
    const lp::lar_term& term() const { return m_term; };
    lp::lconstraint_kind cmp() const { return m_cmp;  };
    const rational& rs() const { return m_rs; };
};

class lemma {
    vector<ineq>     m_ineqs;
    lp::explanation  m_expl;
public:
    void push_back(const ineq& i) { m_ineqs.push_back(i);}
    size_t size() const { return m_ineqs.size() + m_expl.size(); }
    const vector<ineq>& ineqs() const { return m_ineqs; }
    vector<ineq>& ineqs() { return m_ineqs; }
    lp::explanation& expl() { return m_expl; }
    const lp::explanation& expl() const { return m_expl; }
    bool is_conflict() const { return m_ineqs.empty() && !m_expl.empty(); }
};

typedef vector<monomial> polynomial;
// nonlinear integer incremental linear solver
class solver {
    struct imp;
    imp* m_imp;
public:
    // returns the monomial index
    unsigned add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs);
    
    solver(lp::lar_solver& s, reslimit& lim, params_ref const& p);
    ~solver();
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(vector<lemma>&);
    static void test_factorization();
    static void test_basic_sign_lemma();
    static void test_basic_lemma_for_mon_zero_from_monomial_to_factors();
    static void test_basic_lemma_for_mon_zero_from_factors_to_monomial();
    static void test_basic_lemma_for_mon_neutral_from_monomial_to_factors();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
    static void test_order_lemma();
    static void test_order_lemma_params(bool, int sign);
    static void test_monotone_lemma();
    static void test_tangent_lemma();
    static void test_tangent_lemma_reg();
    static void test_tangent_lemma_equiv();
};
}
