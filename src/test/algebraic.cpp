/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    algebraic.cpp

Abstract:

    Test Algebraic Numbers

Author:

    Leonardo (leonardo) 2011-11-22

Notes:

--*/
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial_var2value.h"
#include "util/mpbq.h"
#include "util/rlimit.h"

static void display_anums(std::ostream & out, scoped_anum_vector const & rs) {
    out << "numbers in decimal:\n";
    algebraic_numbers::manager & m = rs.m();
    for (unsigned i = 0; i < rs.size(); i++) {
        m.display_decimal(out, rs[i], 10);
        out << "\n";
    }
    out << "numbers as root objects\n";
    for (unsigned i = 0; i < rs.size(); i++) {
        m.display_root(out, rs[i]);
        out << "\n";
    }
    out << "numbers as intervals\n";
    for (unsigned i = 0; i < rs.size(); i++) {
        m.display_interval(out, rs[i]);
        out << "\n";
    }
}

static void tst1() {
    reslimit rl;
    unsynch_mpq_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    p = 3*x - 2;

    algebraic_numbers::manager am(rl, nm);
    scoped_anum_vector rs1(am);
    std::cout << "p: " << p << "\n";
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
    ENSURE(rs1.size() == 1);
    std::cout.flush();

    p = (x^2) - 2;
    std::cout << "p: " << p << "\n";
    rs1.reset();
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
    ENSURE(rs1.size() == 2);

    scoped_anum sqrt2(am);
    am.set(sqrt2, rs1[1]);

    scoped_mpq  q(nm);
    nm.set(q, 1, 3);
    scoped_anum aq(am);
    am.set(aq, q); // create algebraic number representing 1/3

    am.add(sqrt2, aq, aq);
    std::cout << "sqrt(2) + 1/3: ";
    am.display_decimal(std::cout, aq, 10); std::cout << " "; am.display_interval(std::cout, aq);
    std::cout << " "; am.display_root(std::cout, aq); std::cout << "\n";

    am.set(aq, q);
    am.add(rs1[0], aq, aq);
    std::cout << "-sqrt(2) + 1/3: ";
    am.display_decimal(std::cout, aq, 10); std::cout << " "; am.display_interval(std::cout, aq);
    std::cout << " "; am.display_root(std::cout, aq); std::cout << "\n";

    p = ((x^5) - x - 1)*(x-1)*(x-2);
    std::cout << "p: " << p << "\n";
    rs1.reset();
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
    ENSURE(rs1.size() == 3);

    scoped_anum gauss(am);
    am.set(gauss, rs1[1]);

    std::cout << "compare(" << sqrt2 << ", " << gauss << "): " << am.compare(sqrt2, gauss) << "\n";

    statistics st;
    am.collect_statistics(st);
    st.display_smt2(std::cout);

    p = ((x^2) - 2)*((x^2) - 3);
    std::cout << "p: " << p << "\n";
    rs1.reset();
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
    ENSURE(rs1.size() == 4);

    scoped_anum hidden_sqrt2(am);
    am.set(hidden_sqrt2, rs1[2]);

    std::cout << "compare(" << sqrt2 << ", " << hidden_sqrt2 << "): " << am.compare(sqrt2, hidden_sqrt2) << "\n";
    st.reset();
    am.collect_statistics(st);
    st.display_smt2(std::cout);

    std::cout << "sqrt(2)^4: " << (sqrt2^4) << "\n";

    ENSURE(is_int(power(sqrt2, 4)));
    ENSURE(power(sqrt2, 4) == 4);

    scoped_anum sqrt2_gauss(am);
    am.add(sqrt2, gauss, sqrt2_gauss);
    std::cout << "sqrt2 + gauss: " << sqrt2_gauss << " "; am.display_root(std::cout, sqrt2_gauss); std::cout << "\n";

    std::cout << "sqrt2*sqrt2: " << sqrt2*sqrt2 << "\n";
    std::cout << "sqrt2*sqrt2 == 2: " << (sqrt2*sqrt2 == 2) << std::endl;

    scoped_anum three(am);
    am.set(three, -3);

    std::cout << "(-3)^(1/5): " << root(three, 5) << "\n";
    std::cout << "sqrt(2)^(1/3): " << root(sqrt2, 3) << "\n";
    std::cout << "as-root-object(sqrt(2)^(1/3)): " << root_obj_pp(root(sqrt2, 3)) << "\n";
    std::cout << "(sqrt(2) + 1)^(1/3): " << root(sqrt2 + 1, 3) << "\n";
    std::cout << "as-root-object((sqrt(2) + 1)^(1/3)): " << root_obj_pp(root(sqrt2 + 1, 3)) << "\n";
    std::cout << "(sqrt(2) + gauss)^(1/5): " << root(sqrt2 + gauss, 5) << "\n";
    std::cout << "as-root-object(sqrt(2) + gauss)^(1/5): " << root_obj_pp(root(sqrt2 + gauss, 5)) << "\n";
    std::cout << "(sqrt(2) / sqrt(2)): " << sqrt2 / hidden_sqrt2 << "\n";
    std::cout << "(sqrt(2) / gauss): " << sqrt2 / gauss << "\n";
    std::cout << "(sqrt(2) / gauss) 30 digits: " << decimal_pp(sqrt2 / gauss, 30) << "\n";
    std::cout << "as-root-object(sqrt(2) / gauss): " << root_obj_pp(sqrt2 / gauss) << "\n";
    std::cout << "is_int(sqrt(2)^(1/3)): " << am.is_int(root(sqrt2, 3)) << "\n";

    scoped_anum tmp(am);
    scoped_anum four(am);
    am.set(four, 4);
    am.set(tmp, sqrt2);
    am.inv(tmp);
    std::cout << "1/sqrt(2): " << tmp << "\n";
    am.mul(tmp, four, tmp);
    std::cout << "4*1/sqrt(2): " << tmp << "  " << root_obj_pp(tmp) << "\n";
    am.mul(tmp, sqrt2, tmp);
    std::cout << "sqrt(2)*4*(1/sqrt2): " << tmp << "  " << root_obj_pp(tmp) << "\n";
    std::cout << "is_int(sqrt(2)*4*(1/sqrt2)): " << am.is_int(tmp) << ", after is-int: " << tmp << "\n";

    p = (998*x - 1414)*((x^2) - 15);
    std::cout << "p: " << p << "\n";
    rs1.reset();
    am.isolate_roots(p, rs1);

    std::cout << "is-rational(sqrt2): " << am.is_rational(sqrt2) << "\n";

    scoped_anum qr(am);
    am.set(qr, rs1[1]);

    std::cout << "qr: " << root_obj_pp(qr);
    std::cout << ", is-rational: " << am.is_rational(qr) << ", val: " << root_obj_pp(qr) << "\n";

    return;

    std::cout << "compare(" << sqrt2 << ", " << gauss << "): " << am.compare(sqrt2, gauss) << "\n";

    p = (x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225;
    std::cout << "p: " << p << "\n";
    rs1.reset();
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
}

void tst_refine_mpbq(int n, int d) {
    unsynch_mpq_manager qm;
    mpbq_manager        bqm(qm);
    scoped_mpq q1(qm);
    qm.set(q1, n, d);
    scoped_mpbq l(bqm);
    scoped_mpbq u(bqm);
    std::cout << "using refine upper...\n";
    bqm.to_mpbq(q1, l);
    bqm.set(u, l);
    bqm.mul2(u);
    for (unsigned i = 0; i < 20; i++) {
        std::cout << l << " < " << q1 << " < " << u << "\n";
        bqm.display_decimal(std::cout, l,  20); std::cout << " < ";
        qm.display_decimal(std::cout, q1, 20); std::cout << " < ";
        bqm.display_decimal(std::cout, u, 20); std::cout << std::endl;
        bqm.refine_upper(q1, l, u);
    }
    std::cout << "using refine lower...\n";
    bqm.to_mpbq(q1, l);
    bqm.set(u, l);
    bqm.mul2(u);
    for (unsigned i = 0; i < 20; i++) {
        std::cout << l << " < " << q1 << " < " << u << "\n";
        bqm.display_decimal(std::cout, l,  20); std::cout << " < ";
        qm.display_decimal(std::cout, q1, 20); std::cout << " < ";
        bqm.display_decimal(std::cout, u, 20); std::cout << std::endl;
        bqm.refine_lower(q1, l, u);
    }
}

void tst_refine_mpbq() {
    tst_refine_mpbq(5, 7);
}

void tst_mpbq_root() {
    unsynch_mpq_manager qm;
    mpbq_manager        bqm(qm);
    // scoped_mpbq q(bqm);
    // q.set(q1, 1.4142135 , 7);

}

static void tst_wilkinson() {
    // Test Wilkinson Polynomial
    reslimit rl;
    unsynch_mpq_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    for (int i = 1; i <= 20; i++) {
        if (i > 1)
            p = p*(x - i);
        else
            p = (x - i);
    }
    std::cout << "Wilkinson's polynomial: " << p << "\n";

    algebraic_numbers::manager am(rl, nm);
    scoped_anum_vector rs1(am);
    std::cout << "p: " << p << "\n";
    am.isolate_roots(p, rs1);
    display_anums(std::cout, rs1);
    ENSURE(rs1.size() == 20);
    for (unsigned i = 0; i < rs1.size(); i++) {
        ENSURE(am.is_int(rs1[i]));
    }
}

static void tst_dejan() {
    reslimit rl;
    unsynch_mpq_manager qm;
    algebraic_numbers::manager am(rl, qm);

    scoped_anum two101(am);
    am.set(two101, 2);
    am.root(two101, 11, two101);

    scoped_anum two103(am);
    am.set(two103, 2);
    am.root(two103, 7, two103);

    std::cout << "two101: " << two101 << " " << root_obj_pp(two101) << std::endl;
    std::cout << "two103: " << two103 << " " << root_obj_pp(two103) << std::endl;

    scoped_anum sum1(am);
    am.add(two103, two101, sum1);
    std::cout << "sum1: " << sum1 << " " << root_obj_pp(sum1) << "\n";
}

static void tst_select_small(mpbq_manager & m, scoped_mpbq const & l, scoped_mpbq const & u, bool expected) {
    scoped_mpbq r(m);
    std::cout << "----------\n";
    std::cout << "lower:  " << l << " as decimal: "; m.display_decimal(std::cout, l); std::cout << std::endl;
    std::cout << "upper:  " << u << " as decimal: "; m.display_decimal(std::cout, u); std::cout << std::endl;
    VERIFY(m.select_small(l, u, r) == expected);
    std::cout << "choice: " << r << " as decimal: "; m.display_decimal(std::cout, r); std::cout << std::endl;
}

static void tst_select_small(mpbq_manager & m, int64_t n1, unsigned k1, int64_t n2, unsigned k2, bool expected) {
    scoped_mpbq l(m);
    scoped_mpbq u(m);
    m.set(l, n1, k1);
    m.set(u, n2, k2);
    tst_select_small(m, l, u, expected);
}

static void tst_select_small() {
    unsynch_mpz_manager m;
    mpbq_manager bqm(m);
    tst_select_small(bqm, 1, 3, 3, 2, true);
    tst_select_small(bqm, 10000000000000ll, 40, 11000, 10, true);
    tst_select_small(bqm, 10000000000000ll, 40, 10001, 10, true);
    tst_select_small(bqm, 1, 0, 1, 0, true);
    tst_select_small(bqm, 1, 0, 2, 0, true);
    tst_select_small(bqm, -1, 0, -1, 0, true);
    tst_select_small(bqm, -2, 0, -1, 0, true);
    tst_select_small(bqm, 0, 0, 1100, 10, true);
    tst_select_small(bqm, 7, 3, 1001, 10, true);
    tst_select_small(bqm, 1000, 10, 1001, 10, true);
    scoped_mpbq l1(bqm);
    l1 = 11;
    bqm.power(l1, 64, l1);
    scoped_mpbq l2(bqm);
    l2 = l1 + 1;
    bqm.div2k(l1, 64*3);
    bqm.div2k(l2, 64*3);
    tst_select_small(bqm, l1, l2, true);
    l1 = 11;
    bqm.power(l1, 64, l1);
    l2 = l1 + 256;
    bqm.div2k(l1, 64*3);
    bqm.div2k(l2, 64*3);
    tst_select_small(bqm, l1, l2, true);
}

static void tst_eval_sign(polynomial_ref const & p, anum_manager & am,
                          polynomial::var x0, anum const & v0, polynomial::var x1, anum const & v1, polynomial::var x2, anum const & v2,
                          int expected) {
    polynomial::simple_var2value<anum_manager> x2v(am);
    x2v.push_back(x0, v0);
    x2v.push_back(x1, v1);
    x2v.push_back(x2, v2);
    std::cout << "--------------\n";
    std::cout << "p: " << p << "\n";
    std::cout << "x0 -> "; am.display_root(std::cout, v0); std::cout << "\n";
    std::cout << "x1 -> "; am.display_root(std::cout, v1); std::cout << "\n";
    std::cout << "x2 -> "; am.display_root(std::cout, v2); std::cout << "\n";
    int s = am.eval_sign_at(p, x2v);
    ENSURE((s == 0) == (expected == 0));
    ENSURE((s <  0) == (expected <  0));
    ENSURE((s >  0) == (expected >  0));
    std::cout << "sign: " << s << "\n";
}

static void tst_eval_sign() {
    enable_trace("anum_eval_sign");
    reslimit rl;
    unsynch_mpq_manager        qm;
    polynomial::manager        pm(rl, qm);
    algebraic_numbers::manager am(rl, qm);
    polynomial_ref x0(pm);
    polynomial_ref x1(pm);
    polynomial_ref x2(pm);
    x0 = pm.mk_polynomial(pm.mk_var());
    x1 = pm.mk_polynomial(pm.mk_var());
    x2 = pm.mk_polynomial(pm.mk_var());

    polynomial_ref p(pm);
    p = x0*x1 + (x1^2) + x2 + 2;
    scoped_anum v0(am), v1(am), v2(am);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 1);
    am.set(v2, -2);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 0);
    am.set(v1,  1);
    am.set(v0, -3);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, -1);

    am.set(v0, 2);
    am.root(v0, 2, v0);
    am.set(v1, 0);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 0);
    am.set(v2, 1);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 1);
    am.set(v2, -3);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, -1);

    am.set(v1, 1);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 1);
    am.set(v2, -4);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 1);
    am.set(v2, -5);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, -1);

    am.set(v2, -2);
    am.set(v1, v0);
    am.neg(v1);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 0);

    am.set(v2, -3);
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, -1);
    p = x0*x1 + (x1^2) - x2 + 2;
    tst_eval_sign(p, am, 0, v0, 1, v1, 2, v2, 1);

}

static void tst_isolate_roots(polynomial_ref const & p, anum_manager & am,
                              polynomial::var x0, anum const & v0, polynomial::var x1, anum const & v1, polynomial::var x2, anum const & v2) {
    polynomial::simple_var2value<anum_manager> x2v(am);
    x2v.push_back(x0, v0);
    x2v.push_back(x1, v1);
    x2v.push_back(x2, v2);
    std::cout << "--------------\n";
    std::cout << "p: " << p << "\n";
    std::cout << "x0 -> "; am.display_root(std::cout, v0); std::cout << "\n";
    std::cout << "x1 -> "; am.display_root(std::cout, v1); std::cout << "\n";
    std::cout << "x2 -> "; am.display_root(std::cout, v2); std::cout << "\n";
    scoped_anum_vector roots(am);
    svector<::sign> signs;
    am.isolate_roots(p, x2v, roots, signs);
    ENSURE(roots.size() + 1 == signs.size());
    std::cout << "roots:\n";
    for (unsigned i = 0; i < roots.size(); i++) {
        am.display_root(std::cout, roots[i]); std::cout << " "; am.display_decimal(std::cout, roots[i]); std::cout << "\n";
    }
    std::cout << "signs:\n";
    for (unsigned i = 0; i < signs.size(); i++) {
        if (i > 0)
            std::cout << " 0 ";
        if (signs[i] < 0) std::cout << "-";
        else if (signs[i] == 0) std::cout << "0";
        else std::cout << "+";
    }
    std::cout << "\n";
}

static void tst_isolate_roots() {
    enable_trace("isolate_roots");
    reslimit rl;
    unsynch_mpq_manager        qm;
    polynomial::manager        pm(rl, qm);
    algebraic_numbers::manager am(rl, qm);
    polynomial_ref x0(pm);
    polynomial_ref x1(pm);
    polynomial_ref x2(pm);
    polynomial_ref x3(pm);
    x0 = pm.mk_polynomial(pm.mk_var());
    x1 = pm.mk_polynomial(pm.mk_var());
    x2 = pm.mk_polynomial(pm.mk_var());
    x3 = pm.mk_polynomial(pm.mk_var());

    polynomial_ref p(pm);
    p = x3*x1 + 1;

    scoped_anum v0(am), v1(am), v2(am);

    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    am.set(v1, 1);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    am.set(v1, 2);
    am.root(v1, 2, v1);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 + x2)*x3 + 1;
    am.set(v2, v1);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 + x2)*x3 + x1*x2 + 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 + x2)*(x3^3) + x1*x2 + 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 + x2)*(x3^2) - x1*x2 - 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = x0*(x1 + x2)*(x3^2) - x0*x1*x2 - 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 - x2)*x3 + x1*x2 - 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x1 - x2)*(x3^3) + x1*x2 - 2;
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x3 - x0)*(x3 - x0 - x1);
    am.set(v0, 2);
    am.root(v0, 2, v0); // x2 -> sqrt(2)
    am.set(v1, 3);
    am.root(v1, 2, v1); // x1 -> sqrt(3)
    am.reset(v2);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x3 - x0)*((x3 - x0 - x1)^2);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);

    p = (x3 - x0)*(x3 - 2)*((x3 - 1)^2)*(x3 - x1);
    tst_isolate_roots(p, am, 0, v0, 1, v1, 2, v2);
}

static void pp(polynomial_ref const & p, polynomial::var x) {
    unsigned d = degree(p, x);
    for (unsigned i = 0; i <= d; i++) {
        std::cout << "(" << coeff(p, x, i) << ") ";
    }
    std::cout << "\n";
}

static void ex1() {
    unsynch_mpq_manager        qm;
    reslimit rl;
    polynomial::manager        pm(rl, qm);
    polynomial_ref x(pm);
    polynomial_ref a(pm);
    polynomial_ref b(pm);
    polynomial_ref c(pm);
    x = pm.mk_polynomial(pm.mk_var());
    a = pm.mk_polynomial(pm.mk_var());
    b = pm.mk_polynomial(pm.mk_var());
    c = pm.mk_polynomial(pm.mk_var());
    polynomial_ref p(pm);
    p = (a + 2*b)*(x^3) + x*a + (b^2);
    polynomial_ref p1(pm);
    p1 = derivative(p, 0);
    polynomial_ref h2(pm);
    unsigned d;
    h2 = pseudo_remainder(p, p1, 0, d);
    std::cout << "d: " << d << "\n";
    std::cout << "p: "; pp(p, 0); std::cout << "\np': "; pp(p1, 0); std::cout << "\nh2: "; pp(h2, 0); std::cout << "\n";
    polynomial_ref h3(pm);
    h3 = pseudo_remainder(p1, h2, 0, d);
    std::cout << "d: " << d << "\n";
    std::cout << "h3: "; pp(h3, 0); std::cout << "\n";

    algebraic_numbers::manager am(rl, qm);
    scoped_anum v1(am), v2(am);
    am.set(v1, 2);
    am.root(v1, 3, v1);
    am.set(v2, 3);
    am.root(v2, 3, v2);

    polynomial::simple_var2value<anum_manager> x2v(am);
    x2v.push_back(1, v1);
    x2v.push_back(2, v2);
    std::cout << "sign(h3(v1,v2)): " << am.eval_sign_at(h3, x2v) << "\n";
    scoped_anum v0(am);
    am.set(v0, -1);
    x2v.push_back(0, v0);
    std::cout << "sign(h2(v1,v2)): " << am.eval_sign_at(h2, x2v) << "\n";
    std::cout << "sign(p'(v1,v2)): " << am.eval_sign_at(p1, x2v) << "\n";
    std::cout << "sign(p(v1,v2)): " << am.eval_sign_at(p, x2v) << "\n";

    polynomial::simple_var2value<anum_manager> x2v2(am);
    x2v2.push_back(1, v1);
    x2v2.push_back(2, v2);
    scoped_mpq tmp(qm);
    qm.set(tmp, -1);
    qm.div(tmp, mpz(2), tmp);
    std::cout << "tmp: "; qm.display(std::cout, tmp); std::cout << " "; qm.display_decimal(std::cout, tmp, 10); std::cout << "\n";
    am.set(v0, tmp);
    x2v2.push_back(0, v0);
    std::cout << "v0: " << v0 << "\n";
    std::cout << "sign(h2(v1,v2)): " << am.eval_sign_at(h2, x2v2) << "\n";
    std::cout << "sign(p'(v1,v2)): " << am.eval_sign_at(p1, x2v2) << "\n";
    std::cout << "sign(p(v1,v2)): " << am.eval_sign_at(p, x2v2) << "\n";
}

static void tst_root() {
    reslimit rl;
    unsynch_mpq_manager        qm;
    algebraic_numbers::manager am(rl, qm);
    scoped_anum v1(am), v2(am);
    am.set(v1, 4);
    am.root(v1, 2, v2);
    std::cout << "root: " << v2 << "\n";
    am.set(v1, 4);
    am.root(v1, 4, v2);
    std::cout << "root: " << root_obj_pp(v2) << "\n";

}

void tst_algebraic() {
    // enable_trace("resultant_bug");
    // enable_trace("poly_sign");
    disable_trace("algebraic");
    // enable_trace("mpbq_bug");
    // enable_trace("mpz_mul2k");
    // enable_trace("mpz_gcd");
    tst_root();
    tst_isolate_roots();
    ex1();
    tst_eval_sign();
    tst_select_small();
    tst_dejan();
    tst_wilkinson();
    tst1();
    tst_refine_mpbq();
}
