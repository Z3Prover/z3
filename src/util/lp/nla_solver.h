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
};

typedef vector<ineq> lemma;
typedef vector<monomial> polynomial;
// nonlinear integer incremental linear solver
class solver {
    struct imp;
    imp* m_imp;
public:
    void add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs);
    solver(lp::lar_solver& s, reslimit& lim, params_ref const& p);
    ~solver();
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(lp::explanation&, lemma&);
    static void test_factorization();
    static void test_basic_sign_lemma();
    static void test_basic_lemma_for_mon_zero_from_monomial_to_factors();
    static void test_basic_lemma_for_mon_zero_from_factors_to_monomial();
    static void test_basic_lemma_for_mon_neutral_from_monomial_to_factors();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    static void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
};
}
