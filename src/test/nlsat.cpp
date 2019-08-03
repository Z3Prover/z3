/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat.cpp

Abstract:

    nlsat procedure

Author:

    Leonardo (leonardo) 2012-01-09

Notes:

--*/
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_interval_set.h"
#include "nlsat/nlsat_evaluator.h"
#include "nlsat/nlsat_solver.h"
#include "util/util.h"
#include "nlsat/nlsat_explain.h"
#include "math/polynomial/polynomial_cache.h"
#include "util/rlimit.h"

nlsat::interval_set_ref tst_interval(nlsat::interval_set_ref const & s1,
                                     nlsat::interval_set_ref const & s2,
                                     unsigned expected_num_intervals,
                                     bool check_num_intervals = true) {
    nlsat::interval_set_manager & ism = s1.m();
    nlsat::interval_set_ref r(ism);
    std::cout << "s1:            " << s1 << "\n";
    std::cout << "s2:            " << s2 << "\n";
    r = ism.mk_union(s1, s2);
    std::cout << "union(s1, s2): " << r <<  std::endl;
    ENSURE(!check_num_intervals || ism.num_intervals(r) == expected_num_intervals);
    ENSURE(ism.subset(s1, r));
    ENSURE(ism.subset(s2, r));
    if (ism.set_eq(s1, s2)) {
        ENSURE(ism.set_eq(s1, r));
        ENSURE(ism.set_eq(s2, r));
    }
    else {
        ENSURE(ism.subset(s1, s2) || !ism.subset(r, s2));
        ENSURE(ism.subset(s2, s1) || !ism.subset(r, s1));
    }
    nlsat::interval_set_ref r2(ism);
    r2 = ism.mk_union(s2, s1);
    ENSURE(ism.set_eq(r, r2));
    anum zero;
    nlsat::interval_set_ref full(ism);
    nlsat::literal dummy(131, false);
    full = ism.mk(true, true, zero, true, true, zero, dummy, nullptr);
    ENSURE(ism.set_eq(r, full) == ism.is_full(r));
    return r;
}

static void tst3() {
    enable_trace("nlsat_interval");
    reslimit rl;
    unsynch_mpq_manager         qm;
    anum_manager                am(rl, qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);

    scoped_anum               sqrt2(am), m_sqrt2(am), two(am), m_two(am), three(am), one(am), zero(am);
    am.set(two, 2);
    am.set(m_two, -2);
    am.set(one, 1);
    am.root(two, 2, sqrt2);
    am.set(m_sqrt2, sqrt2);
    am.neg(m_sqrt2);
    am.set(three, 3);

    nlsat::literal p1(1, false);
    nlsat::literal p2(2, false);
    nlsat::literal p3(3, false);
    nlsat::literal p4(4, false);
    nlsat::literal np2(2, true);

    nlsat::interval_set_ref s1(ism), s2(ism), s3(ism), s4(ism);
    s1 = ism.mk_empty();
    std::cout << "s1: " << s1 << "\n";
    s2 = ism.mk(true, true, zero, false, false, sqrt2, np2, nullptr);
    std::cout << "s2: " << s2 << "\n";
    s3 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    std::cout << "s3: " << s3 << "\n";
    s4 = ism.mk_union(s2, s3);
    std::cout << "s4: " << s4 << "\n";

    // Case
    //  s1:   [ ... ]
    //  s2:   [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:   [ ... ]
    // s2: [ ... ]
    s1 = ism.mk(false, false, zero, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, m_sqrt2, false, false, one, p2, nullptr);
    s3 = ism.mk_union(s1, s2);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [ ... ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [ ... ]
    // s2:            [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, one, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);

    // Case
    // s1:   [    ...    ]
    // s2:      [ ... ]
    s1 = ism.mk(false, false, m_sqrt2, false, false, three, p1, nullptr);
    s2 = ism.mk(false, false, zero, false, false, two, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:   [    ...      ]
    // s2:      [ ... ] [  ...  ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, m_sqrt2, false, false, zero, p2, nullptr);
    s3 = ism.mk(false, false, one, false, false, three, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 2);

    // Case
    // s1:  [ ... ]
    // s2:        [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, two, false, false, three, p1, nullptr);
    tst_interval(s1, s2, 1);
    s1 = ism.mk(false, false, m_two, true, false, two, p1, nullptr);
    tst_interval(s1, s2, 2);
    s1 = ism.mk(false, false, two, false, false, two, p1, nullptr);
    s2 = ism.mk(false, false, two, false, false, three, p2, nullptr);
    tst_interval(s1, s2, 1);

    // Case
    // s1:  [ ... ]    [ ...  ]
    // s2: [ .. ]   [ ... ] [ ... ]
    s1 = ism.mk(false, false, m_two, false, false, zero, p1, nullptr);
    s3 = ism.mk(false, false, one, false, false,   three, p1, nullptr);
    s1 = ism.mk_union(s1, s3);
    s2 = ism.mk(true, true, zero,  false, false, m_sqrt2, p2, nullptr);
    tst_interval(s1, s2, 3);
    s3 = ism.mk(false, false, one, false, false, sqrt2, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    s3 = ism.mk(false, false, two, true, true, zero, p2, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 4);

    // Case
    s1 = ism.mk(true, true, zero, false, false, one, p1, nullptr);
    s2 = ism.mk(true, false, one, true, true, zero, p2, nullptr);
    tst_interval(s1, s2, 2);
    s2 = ism.mk(true, false, one, false, false, two, p2, nullptr);
    s3 = ism.mk(false, false, two, true, true, zero, p1, nullptr);
    s2 = ism.mk_union(s2, s3);
    tst_interval(s1, s2, 3);
}

static nlsat::interval_set_ref mk_random(nlsat::interval_set_manager & ism, anum_manager & am, int range, int space, int tries, bool minus_inf, bool plus_inf,
                                       nlsat::literal lit) {
    static random_gen gen;
    ENSURE(range > 0);
    ENSURE(space > 0);
    nlsat::interval_set_ref r(ism), curr(ism);
    scoped_anum lower(am);
    scoped_anum upper(am);
    int prev = -range + (gen() % (space*4));

    if (gen() % 3 == 0 && minus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(upper, next);
        r = ism.mk(true, true, lower, open, false, upper, lit, nullptr);
        prev = next;
    }

    for (int i = 0; i < tries; i++) {
        int l = prev  + (gen() % space);
        int u = l + (gen() % space);
        bool lower_open = gen() % 2 == 0;
        bool upper_open = gen() % 2 == 0;
        if ((lower_open || upper_open) && l == u)
            u++;
        am.set(lower, l);
        am.set(upper, u);
        curr = ism.mk(lower_open, false, lower, upper_open, false, upper, lit, nullptr);
        r = ism.mk_union(r, curr);
        prev = u;
    }

    if (gen() % 3 == 0 && plus_inf) {
        int  next = prev + (gen() % space);
        bool open = gen() % 2 == 0;
        am.set(lower, next);
        curr = ism.mk(open, false, lower, true, true, upper, lit, nullptr);
        r = ism.mk_union(r, curr);
    }
    return r;
}

static void check_subset_result(nlsat::interval_set_ref const & s1,
                                nlsat::interval_set_ref const & s2,
                                nlsat::interval_set_ref const & r,
                                nlsat::literal l1,
                                nlsat::literal l2) {
    nlsat::interval_set_manager ism(s1.m());
    nlsat::interval_set_ref tmp(ism);
    unsigned num = ism.num_intervals(r);
    nlsat::literal_vector lits;
    ptr_vector<nlsat::clause> clauses;
    ism.get_justifications(r, lits, clauses);
    ENSURE(lits.size() <= 2);
    for (unsigned i = 0; i < num; i++) {
        tmp = ism.get_interval(r, i);
        ism.get_justifications(tmp, lits, clauses);
        ENSURE(lits.size() == 1);
        if (lits[0] == l1) {
            ENSURE(ism.subset(tmp, s1));
        }
        else {
            ENSURE(lits[0] == l2);
            ENSURE(ism.subset(tmp, s2));
        }
    }
}

static void tst4() {
    enable_trace("nlsat_interval");
    reslimit rl;
    unsynch_mpq_manager         qm;
    anum_manager                am(rl, qm);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::interval_set_ref     s1(ism), s2(ism), r(ism);

    nlsat::literal l1(1, false);
    nlsat::literal l2(2, false);

    for (unsigned i = 0; i < 100; i++) {
        s1 = mk_random(ism, am, 20, 3, 10, true, true, l1);
        s2 = mk_random(ism, am, 20, 3, 10, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }

    for (unsigned i = 0; i < 100; i++) {
        s1 = mk_random(ism, am, 200, 100, 20, true, true, l1);
        s2 = mk_random(ism, am, 200, 100, 20, true, true, l2);
        r = tst_interval(s1, s2, 0, false);
        check_subset_result(s1, s2, r, l1, l2);
    }
}

static void tst5() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am = s.am();
    nlsat::pmanager & pm = s.pm();
    nlsat::assignment           as(am);
    small_object_allocator      allocator;
    nlsat::interval_set_manager ism(am, allocator);
    nlsat::evaluator            ev(s, as, pm, allocator);
    nlsat::var                  x0, x1;
    x0 = pm.mk_var();
    x1 = pm.mk_var();

    polynomial_ref p(pm);
    polynomial_ref _x0(pm), _x1(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    p = (_x0^2) + (_x1^2) - 2;
    nlsat::poly * _p[1] = { p.get() };
    bool is_even[1] = { false };
    nlsat::bool_var b = s.mk_ineq_atom(nlsat::atom::GT, 1, _p, is_even);
    nlsat::atom * a = s.bool_var2atom(b);
    ENSURE(a != nullptr);
    scoped_anum zero(am);
    am.set(zero, 0);
    as.set(0, zero);
    auto i = ev.infeasible_intervals(a, true, nullptr);
    std::cout << "1) " << i << "\n";
    as.set(1, zero);
    auto i2 = ev.infeasible_intervals(a, true, nullptr);
    std::cout << "2) " << i2 << "\n";
}



static void project(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, unsigned num, nlsat::literal const* lits) {
    std::cout << "Project ";
    s.display(std::cout, num, lits);
    nlsat::scoped_literal_vector result(s);
    ex.project(x, num, lits, result);
    s.display(std::cout << "\n==>\n", result.size(), result.c_ptr());
    std::cout << "\n";
}

static nlsat::literal mk_gt(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::GT, 1, _p, is_even);
}

static nlsat::literal mk_eq(nlsat::solver& s, nlsat::poly* p) {
    nlsat::poly * _p[1] = { p };
    bool is_even[1] = { false };
    return s.mk_ineq_literal(nlsat::atom::EQ, 1, _p, is_even);
}

static void tst6() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = (_a*(_x0^2)) + _x2 + 2;
    p2 = (_b*_x1) - (2*_x2) - _x0 + 8;
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, (_c*_x0) + _x2 + 1));
    lits.push_back(mk_gt(s, (_d*_x0) - _x1 + 5*_x2));

    scoped_anum zero(am), one(am), two(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    as.set(0, one);
    as.set(1, one);
    as.set(2, two);
    as.set(3, two);
    as.set(4, two);
    as.set(5, one);
    as.set(6, one); 
    s.set_rvalues(as);


    project(s, ex, x0, 2, lits.c_ptr());
    project(s, ex, x1, 3, lits.c_ptr());
    project(s, ex, x2, 3, lits.c_ptr());
    project(s, ex, x2, 2, lits.c_ptr());
    project(s, ex, x2, 4, lits.c_ptr());
    project(s, ex, x2, 3, lits.c_ptr()+1);
    
    
}

static void tst7() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    nlsat::pmanager & pm  = s.pm();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);
    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);

    p1 = _x0 + _x1;
    p2 = _x2 - _x0;
    p3 = (-1*_x0) - _x1;
    
    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_gt(s, p1));
    lits.push_back(mk_gt(s, p2));
    lits.push_back(mk_gt(s, p3));

    nlsat::literal_vector litsv(lits.size(), lits.c_ptr());
    lbool res = s.check(litsv);
    VERIFY(res == l_false);
    for (unsigned i = 0; i < litsv.size(); ++i) {
        s.display(std::cout, litsv[i]);
        std::cout << " ";
    }
    std::cout << "\n";

    litsv.reset();
    litsv.append(2, lits.c_ptr());
    res = s.check(litsv);
    ENSURE(res == l_true);
    s.display(std::cout);
    s.am().display(std::cout, s.value(x0)); std::cout << "\n";
    s.am().display(std::cout, s.value(x1)); std::cout << "\n";
    s.am().display(std::cout, s.value(x2)); std::cout << "\n";

}

static void tst8() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var x0, x1, x2, a, b, c, d;
    a  = s.mk_var(false);
    b  = s.mk_var(false);
    c  = s.mk_var(false);
    d  = s.mk_var(false);
    x0 = s.mk_var(false);
    x1 = s.mk_var(false);
    x2 = s.mk_var(false);

    polynomial_ref p1(pm), p2(pm), p3(pm), p4(pm), p5(pm);
    polynomial_ref _x0(pm), _x1(pm), _x2(pm);
    polynomial_ref _a(pm), _b(pm), _c(pm), _d(pm);
    _x0 = pm.mk_polynomial(x0);
    _x1 = pm.mk_polynomial(x1);
    _x2 = pm.mk_polynomial(x2);
    _a  = pm.mk_polynomial(a);
    _b  = pm.mk_polynomial(b);
    _c  = pm.mk_polynomial(c);
    _d  = pm.mk_polynomial(d);
    
    scoped_anum zero(am), one(am), two(am), six(am);
    am.set(zero, 0);
    am.set(one,  1);
    am.set(two,  2);
    am.set(six,  6);
    as.set(0, two); // a
    as.set(1, one); // b
    as.set(2, six); // c
    as.set(3, zero); // d
    as.set(4, zero); // x0
    as.set(5, zero); // x1
    as.set(6, two); // x2
    s.set_rvalues(as);

    nlsat::scoped_literal_vector lits(s);
    lits.push_back(mk_eq(s, (_a*_x2*_x2) - (_b*_x2) - _c));
    project(s, ex, x2, 1, lits.c_ptr());
}



static void tst9() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    int num_lo = 4;
    int num_hi = 5;
    svector<nlsat::var> los, his;
    for (int i = 0; i < num_lo; ++i) {
        los.push_back(s.mk_var(false));
        scoped_anum num(am);
        am.set(num, - i - 1);
        as.set(i, num);
    }
    for (int i = 0; i < num_hi; ++i) {
        his.push_back(s.mk_var(false));
        scoped_anum num(am);
        am.set(num, i + 1);
        as.set(num_lo + i, num);
    }
    nlsat::var _z = s.mk_var(false);
    nlsat::var _x = s.mk_var(false);
    polynomial_ref x(pm), z(pm);
    x = pm.mk_polynomial(_x);
    scoped_anum val(am);
    am.set(val, 0);
    as.set(num_lo + num_hi, val);
    as.set(num_lo + num_hi + 1, val);
    s.set_rvalues(as);
    nlsat::scoped_literal_vector lits(s);

    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, x - z));

#define TEST_ON_OFF()                                   \
    std::cout << "Off ";                                \
    ex.set_signed_project(false);                       \
    project(s, ex, _x, lits.size()-1, lits.c_ptr());    \
    std::cout << "On ";                                 \
    ex.set_signed_project(true);                        \
    project(s, ex, _x, lits.size()-1, lits.c_ptr());    \
    std::cout << "Off ";                                \
    ex.set_signed_project(false);                       \
    project(s, ex, _x, lits.size(), lits.c_ptr());      \
    std::cout << "On ";                                 \
    ex.set_signed_project(true);                        \
    project(s, ex, _x, lits.size(), lits.c_ptr())       \

    TEST_ON_OFF();

    lits.reset();
    polynomial_ref u(pm);
    u = pm.mk_polynomial(his[1]);
    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, u*x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - u*x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, u*x - z));

    TEST_ON_OFF();

    lits.reset();
    u = pm.mk_polynomial(los[1]);
    for (int i = 0; i < num_lo; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(los[i]);
        lits.push_back(mk_gt(s, u*x - y));
    }
    for (int i = 0; i < num_hi; ++i) {
        polynomial_ref y(pm);
        y = pm.mk_polynomial(his[i]);
        lits.push_back(mk_gt(s, y - u*x));
    }
    z = pm.mk_polynomial(_z);
    lits.push_back(mk_eq(s, x - z));

    TEST_ON_OFF();
}


#if 0


#endif

static void test_root_literal(nlsat::solver& s, nlsat::explain& ex, nlsat::var x, nlsat::atom::kind k, unsigned i, nlsat::poly* p) {
    nlsat::scoped_literal_vector result(s);
    ex.test_root_literal(k, x, 1, p, result);
    nlsat::bool_var b = s.mk_root_atom(k, x, i, p);
    s.display(std::cout, nlsat::literal(b, false));
    s.display(std::cout << " ==> ", result.size(), result.c_ptr());
    std::cout << "\n";
}

static bool satisfies_root(nlsat::solver& s, nlsat::atom::kind k, nlsat::poly* p) {
    nlsat::pmanager & pm  = s.pm();
    anum_manager & am     = s.am();
    nlsat::assignment as(am);
    s.get_rvalues(as);
    polynomial_ref pr(p, pm);
    switch (k) {
    case nlsat::atom::ROOT_EQ: return am.eval_sign_at(pr, as) == 0; 
    case nlsat::atom::ROOT_LE: return am.eval_sign_at(pr, as) <= 0;
    case nlsat::atom::ROOT_LT: return am.eval_sign_at(pr, as) <  0;
    case nlsat::atom::ROOT_GE: return am.eval_sign_at(pr, as) >= 0;
    case nlsat::atom::ROOT_GT: return am.eval_sign_at(pr, as) >  0;
    default:
        UNREACHABLE();
        return false;
    }
}

static void tst10() {
    params_ref      ps;
    reslimit        rlim;
    nlsat::solver s(rlim, ps, false);
    anum_manager & am     = s.am();
    nlsat::pmanager & pm  = s.pm();
    nlsat::assignment as(am);
    nlsat::explain& ex    = s.get_explain();
    nlsat::var _a = s.mk_var(false);
    nlsat::var _b = s.mk_var(false);
    nlsat::var _c = s.mk_var(false);
    nlsat::var _x = s.mk_var(false);

    polynomial_ref x(pm), a(pm), b(pm), c(pm), p(pm);
    x = pm.mk_polynomial(_x);
    a = pm.mk_polynomial(_a);
    b = pm.mk_polynomial(_b);
    c = pm.mk_polynomial(_c);
    p = a*x*x + b*x + c;
    scoped_anum one(am), two(am), three(am), mone(am), mtwo(am), mthree(am), zero(am), one_a_half(am);
    am.set(zero, 0);
    am.set(one, 1);
    am.set(two, 2);
    am.set(three, 3);
    am.set(mone, -1);
    am.set(mtwo, -2);
    am.set(mthree, -3);
    rational oah(1,2);
    am.set(one_a_half, oah.to_mpq());
    
 
    scoped_anum_vector nums(am);
    nums.push_back(one);
    nums.push_back(two);
    nums.push_back(one_a_half);
    nums.push_back(mone);
    nums.push_back(three);

    // a = 1, b = -3, c = 2: 
    // has roots x = 2, x = 1:
    //  2^2 - 3*2 + 2 = 0
    //  1 - 3 + 2 = 0
    as.set(_a, one);
    as.set(_b, mthree);
    as.set(_c, two);

    for (unsigned i = 0; i < nums.size(); ++i) {
        as.set(_x, nums[i]);
        s.set_rvalues(as);
        std::cout << p << "\n";
        as.display(std::cout);
        for (unsigned k = nlsat::atom::ROOT_EQ; k <= nlsat::atom::ROOT_GE; ++k) {
            if (satisfies_root(s, (nlsat::atom::kind) k, p)) {
                test_root_literal(s, ex, _x, (nlsat::atom::kind) k, 1, p);
            }
        }
    }
    as.set(_a, mone);
    as.set(_b, three);
    as.set(_c, mtwo);
    for (unsigned i = 0; i < nums.size(); ++i) {
        as.set(_x, nums[i]);
        s.set_rvalues(as);
        std::cout << p << "\n";
        as.display(std::cout);
        for (unsigned k = nlsat::atom::ROOT_EQ; k <= nlsat::atom::ROOT_GE; ++k) {
            if (satisfies_root(s, (nlsat::atom::kind) k, p)) {
                test_root_literal(s, ex, _x, (nlsat::atom::kind) k, 1, p);
            }
        }
    }
    std::cout << "\n";
}

void tst_nlsat() {
    tst10();
    std::cout << "------------------\n";
    tst9();
    std::cout << "------------------\n";
    tst8();
    std::cout << "------------------\n";
    tst7();
    std::cout << "------------------\n";
    tst6();
    std::cout << "------------------\n";
    tst5();
    std::cout << "------------------\n";
    tst4();
    std::cout << "------------------\n";
    tst3();
}
