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
#include "math/lp/nla_solver.h"
namespace nla {
void create_abcde(solver & nla,
                  unsigned lp_a,
                  unsigned lp_b,
                  unsigned lp_c,
                  unsigned lp_d,
                  unsigned lp_e,
                  unsigned lp_abcde,
                  unsigned lp_ac,
                  unsigned lp_bde,
                  unsigned lp_acd,
                  unsigned lp_be) {
    // create monomial abcde
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monic(lp_abcde, vec.size(), vec.begin());

    // create monomial ac
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    nla.add_monic(lp_ac, vec.size(), vec.begin());

    // create monomial bde
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);
    nla.add_monic(lp_bde, vec.size(), vec.begin());

    // create monomial acd
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monic(lp_acd, vec.size(), vec.begin());

    // create monomial be
    vec.clear();
    vec.push_back(lp_b);
    vec.push_back(lp_e);
    nla.add_monic(lp_be, vec.size(), vec.begin());
}


void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0\n";
    enable_trace("nla_solver");
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    
    reslimit l;
    params_ref p;
    solver nla(s);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monic(lp_bde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_b);v.push_back(lp_c);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monic(lp_abcde, v.size(), v.begin());
    v.clear();
    v.push_back(lp_a);v.push_back(lp_c);
    nla.add_monic(lp_ac, v.size(), v.begin());
     
    vector<lemma> lv;

    // set abcde = ac * bde
    // ac = 1 then abcde = bde, but we have abcde < bde
    s.set_column_value(lp_a, lp::impq(rational(4)));
    s.set_column_value(lp_b, lp::impq(rational(4)));
    s.set_column_value(lp_c, lp::impq(rational(4)));
    s.set_column_value(lp_d, lp::impq(rational(4)));
    s.set_column_value(lp_e, lp::impq(rational(4)));
    s.set_column_value(lp_abcde, lp::impq(rational(15)));
    s.set_column_value(lp_ac, lp::impq(rational(1)));
    s.set_column_value(lp_bde, lp::impq(rational(16)));

    
    SASSERT(nla.get_core()->test_check(lv) == l_false);
    
    nla.get_core()->print_lemma(std::cout);

    ineq i0(llc::NE, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_ac);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_bde);
    i1.m_term.add_monomial(-rational(1), lp_abcde);
    ineq i2(llc::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_var(lp_abcde);
    i2.m_term.add_monomial(-rational(1), lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    for (const auto& k : lv[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } 
    }

    SASSERT(found0 && (found1 || found2));

    
}

void s_set_column_value(lp::lar_solver&s, lpvar j, const rational & v) {
    s.set_column_value(j, lp::impq(v));
}

void s_set_column_value(lp::lar_solver&s, lpvar j, const lp::impq & v) {
    s.set_column_value(j, v);
}

void test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1\n";
    TRACE("nla_solver",);
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7;
    lpvar lp_a = s.add_var(a, true);
    lpvar lp_b = s.add_var(b, true);
    lpvar lp_c = s.add_var(c, true);
    lpvar lp_d = s.add_var(d, true);
    lpvar lp_e = s.add_var(e, true);
    lpvar lp_bde = s.add_var(bde, true);
    
    reslimit l;
    params_ref p;
    solver nla(s);
    svector<lpvar> v; v.push_back(lp_b);v.push_back(lp_d);v.push_back(lp_e);
    nla.add_monic(lp_bde, v.size(), v.begin());

    vector<lemma> lemma;

    s_set_column_value(s, lp_a, rational(1));
    s_set_column_value(s, lp_b, rational(1));
    s_set_column_value(s, lp_c, rational(1));
    s_set_column_value(s, lp_d, rational(1));
    s_set_column_value(s, lp_e, rational(1));
    s_set_column_value(s, lp_bde, rational(3));

    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    SASSERT(lemma[0].size() == 4);
    nla.get_core()->print_lemma(std::cout);

    ineq i0(llc::NE, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_b);
    ineq i1(llc::NE, lp::lar_term(), rational(1));
    i1.m_term.add_var(lp_d);
    ineq i2(llc::NE, lp::lar_term(), rational(1));
    i2.m_term.add_var(lp_e);
    ineq i3(llc::EQ, lp::lar_term(), rational(1));
    i3.m_term.add_var(lp_bde);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;
    bool found3 = false;
    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2) {
            found2 = true;
        } else if (k == i3) {
            found3 = true;
        }

    }

    SASSERT(found0 && found1 && found2 && found3);

}
void test_basic_lemma_for_mon_neutral_from_factors_to_monomial() {
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_0();
    test_basic_lemma_for_mon_neutral_from_factors_to_monomial_1();
}


void test_basic_lemma_for_mon_zero_from_factors_to_monomial() {
    std::cout << "test_basic_lemma_for_mon_zero_from_factors_to_monomial\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    lpvar lp_be = s.add_named_var(be, true, "be");
    
    reslimit l;
    params_ref p;
    solver nla(s);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<lemma> lemma;

    // set vars
    s_set_column_value(s, lp_a, rational(1));
    s_set_column_value(s, lp_b, rational(0));
    s_set_column_value(s, lp_c, rational(1));
    s_set_column_value(s, lp_d, rational(1));
    s_set_column_value(s, lp_e, rational(1));
    s_set_column_value(s, lp_abcde, rational(0));
    s_set_column_value(s, lp_ac, rational(1));
    s_set_column_value(s, lp_bde, rational(0));
    s_set_column_value(s, lp_acd, rational(1));
    s_set_column_value(s, lp_be, rational(1));

    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    nla.get_core()->print_lemma(std::cout);
    SASSERT(lemma.size() == 1 && lemma[0].size() == 2);
    ineq i0(llc::NE, lp::lar_term(), rational(0));
    i0.m_term.add_var(lp_b);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_be);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void test_basic_lemma_for_mon_zero_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_zero_from_monomial_to_factors\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, c = 2, d = 3, acd = 8;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    
    reslimit l;
    params_ref p;
    solver nla(s);

    // create monomial acd
    unsigned_vector vec;
    vec.clear();
    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    nla.add_monic(lp_acd, vec.size(), vec.begin());
    
    vector<lemma> lemma;
    s_set_column_value(s, lp_a, rational(1));
    s_set_column_value(s, lp_c, rational(1));
    s_set_column_value(s, lp_d, rational(1));
    s_set_column_value(s, lp_acd, rational(0));

    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    
    nla.get_core()->print_lemma(std::cout);

    ineq i0(llc::EQ, lp::lar_term(), rational(0));
    i0.m_term.add_var(lp_a);
    ineq i1(llc::EQ, lp::lar_term(), rational(0));
    i1.m_term.add_var(lp_c);
    ineq i2(llc::EQ, lp::lar_term(), rational(0));
    i2.m_term.add_var(lp_d);
    bool found0 = false;
    bool found1 = false;
    bool found2 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        } else if (k == i2){
            found2 = true;
        }
    }

    SASSERT(found0 && found1 && found2);
    
}

void test_basic_lemma_for_mon_neutral_from_monomial_to_factors() {
    std::cout << "test_basic_lemma_for_mon_neutral_from_monomial_to_factors\n";
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        abcde = 5, ac = 6, bde = 7, acd = 8, be = 9;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_abcde = s.add_named_var(abcde, true, "abcde");
    lpvar lp_ac = s.add_named_var(ac, true, "ac");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    lpvar lp_be = s.add_named_var(be, true, "be");
    
    reslimit l;
    params_ref p;
    solver nla(s);
    
    create_abcde(nla,
                 lp_a,
                 lp_b,
                 lp_c,
                 lp_d,
                 lp_e,
                 lp_abcde,
                 lp_ac,
                 lp_bde,
                 lp_acd,
                 lp_be);
    vector<lemma> lemma;

    // set all vars to 1
    s_set_column_value(s, lp_a, rational(1));
    s_set_column_value(s, lp_b, rational(1));
    s_set_column_value(s, lp_c, rational(1));
    s_set_column_value(s, lp_d, rational(1));
    s_set_column_value(s, lp_e, rational(1));
    s_set_column_value(s, lp_abcde, rational(1));
    s_set_column_value(s, lp_ac, rational(1));
    s_set_column_value(s, lp_bde, rational(1));
    s_set_column_value(s, lp_acd, rational(1));
    s_set_column_value(s, lp_be, rational(1));

    // set bde to 2, b to minus 2
    s_set_column_value(s, lp_bde, rational(2));
    s_set_column_value(s, lp_b, - rational(2));
    // we have bde = -b, therefore d = +-1 and e = +-1
    s_set_column_value(s, lp_d,  rational(3));
    SASSERT(nla.get_core()->test_check(lemma) == l_false);

    
    nla.get_core()->print_lemma(std::cout);
    ineq i0(llc::EQ, lp::lar_term(), rational(1));
    i0.m_term.add_var(lp_d);
    ineq i1(llc::EQ, lp::lar_term(), -rational(1));
    i1.m_term.add_var(lp_d);
    bool found0 = false;
    bool found1 = false;

    for (const auto& k : lemma[0].ineqs()){
        if (k == i0) {
            found0 = true;
        } else if (k == i1) {
            found1 = true;
        }
    }

    SASSERT(found0 && found1);
}

void test_horner() {
    enable_trace("nla_solver");
    /*    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        ce = 5, bd = 6, ab = 7, ac = 8, c_min_b = 9;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_ce = s.add_named_var(ce, true, "ce");
    lpvar lp_bd = s.add_named_var(bd, true, "ab");
    lpvar lp_ac = s.add_named_var(ac, true, "ce");

    lp::lar_term t;
    t.add_var(lp_c);
    t.add_monomial(rational(-1), lp_b);
    lpvar lp_c_min_b = s.add_term(t.coeffs_as_vector(), c_min_b);
    
    reslimit l;
    params_ref p;
    solver nla(s);
    vector<lpvar> v;
    v.push_back(a); v.push_back(b);
    nla.add_monic(lp_ab, v.size(), v.begin());
    v.clear();

    v.push_back(c); v.push_back(e);
    nla.add_monic(lp_ce, v.size(), v.begin());
    v.clear();

    v.push_back(b); v.push_back(d);
    nla.add_monic(lp_bd, v.size(), v.begin());
    v.clear();

    v.push_back(a); v.push_back(c);
    nla.add_monic(lp_ac, v.size(), v.begin());
    v.clear();

    */


}
void test_basic_sign_lemma() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4,
        bde = 7, acd = 8;
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_bde = s.add_named_var(bde, true, "bde");
    lpvar lp_acd = s.add_named_var(acd, true, "acd");
    
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial bde
    vector<unsigned> vec;

    vec.push_back(lp_b);
    vec.push_back(lp_d);
    vec.push_back(lp_e);

    nla.add_monic(lp_bde, vec.size(), vec.begin());
    vec.clear();

    vec.push_back(lp_a);
    vec.push_back(lp_c);
    vec.push_back(lp_d);

    nla.add_monic(lp_acd, vec.size(), vec.begin());

    // set the values of the factors so it should be bde = -acd according to the model
    
    // b = -a
    s_set_column_value(s, lp_a, rational(7));
    s_set_column_value(s, lp_b, rational(-7));
    
    // e - c = 0
    s_set_column_value(s, lp_e, rational(4));
    s_set_column_value(s, lp_c, rational(4));

    s_set_column_value(s, lp_d, rational(6));

    //    make bde != -acd according to the model
    s_set_column_value(s, lp_bde, rational(5));
    s_set_column_value(s, lp_acd, rational(3));
   
    vector<lemma> lemmas;
    SASSERT(nla.get_core()->test_check(lemmas) == l_false);

    lp::lar_term t;
    t.add_var(lp_bde);
    t.add_var(lp_acd);
    ineq q(llc::EQ, t, rational(0));
   
    nla.get_core()->print_lemma(std::cout);
}

void test_order_lemma_params(bool var_equiv, int sign) {
    /*    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, abef = 13, cdij = 16, ij = 17,
        k = 18;
    
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_f = s.add_named_var(f, true, "f");
    lpvar lp_i = s.add_named_var(i, true, "i");
    lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_k = s.add_named_var(k, true, "k");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_cd = s.add_named_var(cd, true, "cd");
    lpvar lp_ef = s.add_named_var(ef, true, "ef");
    lpvar lp_ij = s.add_named_var(ij, true, "ij");
    lpvar lp_abef = s.add_named_var(abef, true, "abef");
    lpvar lp_cdij = s.add_named_var(cdij, true, "cdij");

    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s_set_column_value(s, j, rational(j + 2));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monic(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    int mon_cd = nla.add_monic(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    int mon_ef = nla.add_monic(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    if (var_equiv)
        vec.push_back(lp_k);
    else
        vec.push_back(lp_j);
    int mon_ij = nla.add_monic(lp_ij, vec.size(), vec.begin());

    if (var_equiv) { // make k equivalent to j
        lp::lar_term t;
        t.add_var(lp_k);
        t.add_monomial(-rational(1), lp_j);
        lpvar kj = s.add_term(t.coeffs_as_vector(), -1);
        s.add_var_bound(kj, llc::LE, rational(0));
        s.add_var_bound(kj, llc::GE, rational(0));
    }
    
    //create monomial (ab)(ef) 
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    vec.push_back(lp_f);
    nla.add_monic(lp_abef, vec.size(), vec.begin());

    //create monomial (cd)(ij)
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    auto mon_cdij = nla.add_monic(lp_cdij, vec.size(), vec.begin());

    // set i == e
    s_set_column_value(s, lp_e, s.get_column_value(lp_i));
    // set f == sign*j
    s_set_column_value(s, lp_f, rational(sign) * s.get_column_value(lp_j));
    if (var_equiv) {
        s_set_column_value(s, lp_k, s.get_column_value(lp_j));
    }
    // set the values of ab, ef, cd, and ij correctly
    s_set_column_value(s, lp_ab, nla.get_core()->mon_value_by_vars(mon_ab));
    s_set_column_value(s, lp_ef, nla.get_core()->mon_value_by_vars(mon_ef));
    s_set_column_value(s, lp_cd, nla.get_core()->mon_value_by_vars(mon_cd));
    s_set_column_value(s, lp_ij, nla.get_core()->mon_value_by_vars(mon_ij));
   
    // set abef = cdij, while it has to be abef < cdij
    if (sign > 0) {
        SASSERT(s.get_column_value(lp_ab) < s.get_column_value(lp_cd));
        // we have ab < cd

        // we need to have ab*ef < cd*ij, so let us make ab*ef > cd*ij
        s_set_column_value(s, lp_cdij, nla.get_core()->mon_value_by_vars(mon_cdij));
        s_set_column_value(s, lp_abef, nla.get_core()->mon_value_by_vars(mon_cdij)
                           + rational(1));
        
    }
    else {
        SASSERT(-s.get_column_value(lp_ab) < s.get_column_value(lp_cd));
        // we need to have abef < cdij, so let us make abef < cdij
        s_set_column_value(s, lp_cdij, nla.get_core()->mon_value_by_vars(mon_cdij));
        s_set_column_value(s, lp_abef, nla.get_core()->mon_value_by_vars(mon_cdij)
                           + rational(1));
    }
    vector<lemma> lemma;

    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    // lp::lar_term t;
    // t.add_monomial(lp_bde);
    // t.add_monomial(lp_acd);
    // ineq q(llc::EQ, t, rational(0));
   
    nla.get_core()->print_lemma(std::cout);
    // SASSERT(q == lemma.back());
    // ineq i0(llc::EQ, lp::lar_term(), rational(0));
    // i0.m_term.add_monomial(lp_bde);
    // i0.m_term.add_monomial(rational(1), lp_acd);
    // bool found = false;
    // for (const auto& k : lemma){
    //     if (k == i0) {
    //         found = true;
    //     } 
    // }

    // SASSERT(found);
    */
}

void test_monotone_lemma() {
    /*
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, 
        i = 8, j = 9,
        ab = 10, cd = 11, ef = 12, ij = 17;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_c = s.add_named_var(c, true, "c");
    lpvar lp_d = s.add_named_var(d, true, "d");
    lpvar lp_e = s.add_named_var(e, true, "e");
    lpvar lp_f = s.add_named_var(f, true, "f");
    lpvar lp_i = s.add_named_var(i, true, "i");
    lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    lpvar lp_cd = s.add_named_var(cd, true, "cd");
    lpvar lp_ef = s.add_named_var(ef, true, "ef");
    lpvar lp_ij = s.add_named_var(ij, true, "ij");
    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        s_set_column_value(s, j, rational((j + 2)*(j + 2)));
    }
    
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monic(lp_ab, vec.size(), vec.begin());
    // create monomial cd
    vec.clear();
    vec.push_back(lp_c);
    vec.push_back(lp_d);
    int mon_cd = nla.add_monic(lp_cd, vec.size(), vec.begin());
    // create monomial ef
    vec.clear();
    vec.push_back(lp_e);
    vec.push_back(lp_f);
    nla.add_monic(lp_ef, vec.size(), vec.begin());
    // create monomial ij
    vec.clear();
    vec.push_back(lp_i);
    vec.push_back(lp_j);
    int mon_ij = nla.add_monic(lp_ij, vec.size(), vec.begin());

    // set e == i + 1
    s_set_column_value(s, lp_e, s.get_column_value(lp_i) + lp::impq(rational(1)));
    // set f == j + 1
    s_set_column_value(s, lp_f, s.get_column_value(lp_j) +lp::impq( rational(1)));
    // set the values of ab, ef, cd, and ij correctly
    
    s_set_column_value(s, lp_ab, nla.get_core()->mon_value_by_vars(mon_ab));
    s_set_column_value(s, lp_cd, nla.get_core()->mon_value_by_vars(mon_cd));
    s_set_column_value(s, lp_ij, nla.get_core()->mon_value_by_vars(mon_ij));
   
    // set ef = ij while it has to be ef > ij
    s_set_column_value(s, lp_ef, s.get_column_value(lp_ij));

    vector<lemma> lemma;
    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    nla.get_core()->print_lemma(std::cout);
    */
}

void test_tangent_lemma_rat() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = s.number_of_vars();
    unsigned b = a + 1;
    unsigned ab = b + 1;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, false, "b");
    lpvar lp_ab = s.add_named_var(ab, false, "ab");
    s_set_column_value(s, lp_a, rational(3));
    s_set_column_value(s, lp_b, rational(4));
    rational v = rational(12) + rational (1)/rational(7);
    s_set_column_value(s, lp_ab, v);
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    nla.add_monic(lp_ab, vec.size(), vec.begin());
    
    vector<lemma> lemma;
    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    nla.get_core()->print_lemma(std::cout);
}

void test_tangent_lemma_reg() {
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = s.number_of_vars();
    unsigned b = a + 1;
    unsigned ab = b + 1;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_b = s.add_named_var(b, true, "b");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    s_set_column_value(s, lp_a, rational(3));
    s_set_column_value(s, lp_b, rational(4));
    s_set_column_value(s, lp_ab, rational(11));
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    nla.add_monic(lp_ab, vec.size(), vec.begin());
    
    vector<lemma> lemma;
    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    nla.get_core()->print_lemma(std::cout);
}

void test_tangent_lemma_equiv() {
    /*
    enable_trace("nla_solver");
    lp::lar_solver s;
    unsigned a = 0, b = 1, k = 2, ab = 10;
    
    lpvar lp_a = s.add_named_var(a, true, "a");
    lpvar lp_k = s.add_named_var(k, true, "k");
    lpvar lp_b = s.add_named_var(b, true, "b");
    //    lpvar lp_c = s.add_named_var(c, true, "c");
    //    lpvar lp_d = s.add_named_var(d, true, "d");
    // lpvar lp_e = s.add_named_var(e, true, "e");
    // lpvar lp_f = s.add_named_var(f, true, "f");
    // lpvar lp_i = s.add_named_var(i, true, "i");
    // lpvar lp_j = s.add_named_var(j, true, "j");
    lpvar lp_ab = s.add_named_var(ab, true, "ab");
    int sign = 1;
    for (unsigned j = 0; j < s.number_of_vars(); j++) {
        sign *= -1;
        s_set_column_value(s, j, sign * rational((j + 2) * (j + 2)));
    }

    // make k == -a
    lp::lar_term t;
    t.add_var(lp_k);
    t.add_var(lp_a);
    lpvar kj = s.add_term(t.coeffs_as_vector(), -1);
    s.add_var_bound(kj, llc::LE, rational(0)); 
    s.add_var_bound(kj, llc::GE, rational(0));
    s_set_column_value(s, lp_a, - s.get_column_value(lp_k));
    reslimit l;
    params_ref p;
    solver nla(s);
    // create monomial ab
    vector<unsigned> vec;
    vec.push_back(lp_a);
    vec.push_back(lp_b);
    int mon_ab = nla.add_monic(lp_ab, vec.size(), vec.begin());
    
    s_set_column_value(s, lp_ab, nla.get_core()->mon_value_by_vars(mon_ab) + rational(10)); // greater by ten than the correct value
    vector<lemma> lemma;

    SASSERT(nla.get_core()->test_check(lemma) == l_false);
    nla.get_core()->print_lemma(std::cout);
    */
}


void test_tangent_lemma() {
    test_tangent_lemma_rat();
    test_tangent_lemma_reg();    
    test_tangent_lemma_equiv();    
}

void test_order_lemma() {
    test_order_lemma_params(false,  1);
    test_order_lemma_params(false, -1);
    test_order_lemma_params(true,   1);
    test_order_lemma_params(true,  -1);
}


} // end of namespace nla
