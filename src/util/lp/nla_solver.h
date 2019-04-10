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
#include "util/lp/nla_core.h"
namespace nla {

// nonlinear integer incremental linear solver
class solver {
    core* m_core;
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
    static void s_set_column_value(lp::lar_solver&, unsigned, const rational &);
    static void s_set_column_value(lp::lar_solver&, unsigned, const lp::impq &);
};
}
