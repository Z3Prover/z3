/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial.cpp

Abstract:

    Goodies for creating and handling polynomials.

Author:

    Leonardo (leonardo) 2011-11-15

Notes:

--*/
#if !defined(__clang__)
#include"polynomial.h"
#include"polynomial_var2value.h"
#include"polynomial_cache.h"
#include"linear_eq_solver.h"
#include"rlimit.h"

static void tst1() {
    std::cout << "\n----- Basic testing -------\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    std::cout << x0 << " " << x1 << " " << x2 << "\n";
    polynomial_ref p(m);
    p = (x0^3) + x1*x0 + 2;
    std::cout << p << "\n";
    std::cout << "max_var(p): " << max_var(p) << "\n";
    SASSERT(max_var(p) == 1);
    std::cout << (2*x2 - x1*x0) << "\n";
    std::cout << (p + (2*x2 - x1*x0)) << "\n";
    std::cout << (p*p + 2*x2) << "\n";
    std::cout << derivative(p*p + 2*x2, 0) << "\n";
    polynomial_ref q(m);
    q = (x0^4) + x0 + 1;
    std::cout << "q(x): " << q << "\n";
    std::cout << "q(y): " << compose_y(q, 2) << "\n";
    std::cout << "q(x-y): " << compose_x_minus_y(q, 2) << "\n";
    q = (x0 - 1)*(x0 - 2)*(x0 - 1)*(x0 + 2);
    std::cout << "q: " << q << "\n";
    polynomial_ref s(m);
    s = (x0 - 1)*((x0 + 3)^2);
    std::cout << "s: " << s << "\n";
}

static void tst_pseudo_div(polynomial_ref const & A, polynomial_ref const & B, polynomial::var x) {
    reslimit rl;
    polynomial::manager & m = A.m();
    std::cout << "---- Pseudo-division test ----\n";
    std::cout << "A: " << A << "\n";
    std::cout << "B: " << B << "\n";
    std::cout << "x: " << x << "\n";
    polynomial_ref Q(m);
    polynomial_ref R(m);
    unsigned d;
    Q = pseudo_division(A, B, x, d, R);
    std::cout << "d: " << d << "\n";
    std::cout << "Q: " << Q << "\n";
    std::cout << "R: " << R << "\n";
    polynomial_ref l_B(m);
    l_B = coeff(B, x, degree(B, x));
    std::cout << "l_B: " << l_B << "\n";
    polynomial_ref l_B_d(m);
    l_B_d = l_B^d;
    polynomial_ref t(m);
    std::cout << "l_B^d: " << l_B_d << "\n";
    std::cout << "Q * B + R: " << Q * B + R << "\n";
    std::cout << "l_B_d * A: " << l_B_d * A << "\n";
    SASSERT(eq((Q * B + R), (l_B_d * A)));
}

static void tst2() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = ((x0 - 1)^2)*x2 + (x1^2)*((x2 - 2)^2) + 1;
    q = (x0 - 1)*x2 + (x1^3)*(x2 - 2) + (x0 - 2)*(x1 - 2) + 10;
    tst_pseudo_div(p, q, 0);
}


static void tst3() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (x1^2) + (x0^2) - 1;
    q = (x1*x0) - 1;
    tst_pseudo_div(p, q, 1);
}

static void tst4() {
    std::cout << "---- Testing renaming/reordering ----\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p1 = x2 + ((x0 - 1)^2)*x1 + (x2^3) + 10;
    polynomial_ref p2 = x0*x1*x2 + x1*(x2^3) + ((x0 - 2)^2);
    std::cout << "p1: " << p1 << "\n";
    std::cout << "p2: " << p2 << "\n";
    polynomial::var new_order[3] = { 2, 0, 1 };
    m.rename(3, new_order);
    std::cout << "----- x0 -> x2, x1 -> x0, x2 -> x1 \n";
    std::cout << "p1: " << p1 << "\n";
    std::cout << "p2: " << p2 << "\n";
}

static void tst_quasi_resultant(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x) {
    std::cout << "---- Testing quasi-resultants ---- \n";
    std::cout << "p : " << p << "\n";
    std::cout << "q : " << q << "\n";
    std::cout << "x : " << x << "\n--->\n";
    std::cout << quasi_resultant(p, q, x) << "\n";
}

static void tst5() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = ((x0 - x1)^2) - 2;
    q = (x1^2) - 3;
    // sqrt(2) + sqrt(3) must be a root of the quasi-resultant
    tst_quasi_resultant(p, q, 1);
}

static void tst6() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (x0 - 2)*(x0 - 3)*(x0 + 2);
    std::cout << "p(x0):         " << p << "\n";
    std::cout << "p(-x0):        " << compose_minus_x(p) << "\n";
    std::cout << "x^3*p(1/x0):   " << compose_1_div_x(p) << "\n";
    std::cout << "p(x0 - x1):    " << compose_x_minus_y(p, 1) << "\n";
    std::cout << "x1^3*p(x0/x1): " << compose_x_div_y(p, 1) << "\n";
}

static void tst7() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q1(m);
    polynomial_ref q2(m);
    p  = (x0 - x1)*(x2 - 1);
    q1 = (x0^2) - 2;
    q2 = (x1^2) - 2;
    polynomial_ref r(m);
    r  = quasi_resultant(p, q1, 0);
    std::cout << "1) r: " << r << "\n";
    r  = quasi_resultant(r, q2, 1);
    std::cout << "2) r: " << r << "\n";
}

static void tst8() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref sqrt2(m);
    polynomial_ref sqrt3(m);
    p     = x2 - (x0*x1 - (x0^2) + 1);
    sqrt3 = (x0^2) - 3;
    sqrt2 = (x1^2) - 2;
    polynomial_ref r(m);
    r  = quasi_resultant(p, sqrt2, 1);
    r  = quasi_resultant(r, sqrt3, 0);
    std::cout << "r: " << r << "\n";
}


static void tst9() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref sqrt2(m);
    p     = ((x0^3) - 1)*(x1^2) - 1;
    sqrt2 = ((x0^2) - 2)*(x0 - 2); // added garbage to polynomial
    // sqrt2 = (x0^2) - 2; // added garbage to polynomial
    // p(sqrt(2), x1) has the roots  -0.7395 and 0.7395
    polynomial_ref r(m);
    r  = quasi_resultant(p, sqrt2, 0);
    std::cout << "p: " << p << "\n";
    std::cout << "sqrt2: " << sqrt2 << "\n";
    std::cout << "r: " << r << "\n";
    // r contains the roots -0.7395 and 0.7395, plus garbage roots: 0, -0.3779, 0.3779
    polynomial_ref q(m);
    q  = x2 - (((x0^3) - 1)*(x1^2) - 1);
    std::cout << "q: " << q << "\n";
    polynomial_ref r2(m);
    TRACE("polynomial", tout << "QUASI_RESULTANT: q, sqrt2.....\n";);
    r2  = quasi_resultant(q, sqrt2, 0);
    // TRACE("polynomial", tout << "QUASI_RESULTANT: sqrt2, q.....\n";);
    // std::cout << "r2: " << r2 << "\n";
    // r2  = quasi_resultant(sqrt2, q, 0);
    // std::cout << "r2: " << r2 << "\n";
    // return;
    std::cout << "r2: " << r2 << "\n";
    r2  = normalize(quasi_resultant(r2, r, 1));
    std::cout << "r2: " << r2 << "\n";
    polynomial_ref_vector seq(m);
    r2  = normalize(quasi_resultant(sqrt2, q, 0));
    // sturm_seq(r2, seq);
    std::cout << "r2:\n" << r2 << "\n";
}

static void tst10() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial_ref A(m);
    polynomial_ref B(m);
    polynomial_ref g(m);
    polynomial_ref h(m);
    polynomial_ref R(m);
    A  = x2 - (((x0^3) - 1)*(x1^2) - 1);
    B  = ((x0^2) - 2)*(x0 - 2);
    std::cout << "A: " << A << "\nB: " << B << "\n";
    unsigned d;
    R  = pseudo_remainder(A, B, 0, d);
    std::cout << "R: " << R << "\n";
    // second iteration
    std::cout << "second iteration...\n";
    A  = B;
    B  = R;
    g  = coeff(A, 0, degree(A, 0));
    std::cout << "A: " << A << "\nB: " << B << "\ng: " << g << "\n";
    R  = pseudo_remainder(A, B, 0, d);
    std::cout << "R: " << R << "\n";
    // third iteration
    std::cout << "third iteration...\n";
    A  = B;
    B  = R;
    g  = coeff(A, 0, degree(A, 0));
    std::cout << "A: " << A << "\nB: " << B << "\ng: " << g << "\n";
    R  = pseudo_remainder(A, B, 0, d);
    std::cout << "R: " << R << "\n";

}

static void tst11() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    q  = ((x1^2) + 1)*(x2 + 1);
    p  = (x3 + 1)*q;
    polynomial_ref d(m);
    d = exact_div(p, q);
    std::cout << "p: " << p << "\nq: " << q << "\nd: " << d << "\n";
    SASSERT(eq(q * d, p));

    q  = ((x1^3) + x1 + 1)*((x2^2) + x2 + x2 + 1)*((x3^2) + 2);
    p  = (x1 + (x3^2) + x3 + x2 + (x2^2) + 1)*((x1^3) + x1 + 1)*((x2^2) + x2 + x2 + 1)*((x3^2) + 2);
    d = exact_div(p, q);
    std::cout << "p: " << p << "\nq: " << q << "\nd: " << d << "\n";
    SASSERT(eq(q * d, p));
}

static void tst_discriminant(polynomial_ref const & p, polynomial::var x, polynomial_ref const & expected) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    r = discriminant(p, x);
    std::cout << "r: " << r << "\n";
    std::cout << "expected: " << expected << "\n";
    SASSERT(eq(r, expected));
    m.lex_sort(r);
    std::cout << "r (sorted): " << r << "\n";
}

static void tst_discriminant(polynomial_ref const & p, polynomial_ref const & expected) {
    tst_discriminant(p, max_var(p), expected);
}

static void tst_discriminant() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref a(m);
    polynomial_ref b(m);
    polynomial_ref c(m);
    polynomial_ref d(m);
    polynomial_ref x(m);
    a = m.mk_polynomial(m.mk_var());
    b = m.mk_polynomial(m.mk_var());
    c = m.mk_polynomial(m.mk_var());
    d = m.mk_polynomial(m.mk_var());
    x = m.mk_polynomial(m.mk_var());
    tst_discriminant(a*(x^2) + b*x  + c,
                     (b^2) - 4*a*c);
    tst_discriminant(a*(x^3) + b*(x^2) + c*x + d,
                     (b^2)*(c^2) - 4*a*(c^3) - 4*(b^3)*d + 18*a*b*c*d - 27*(a^2)*(d^2));
    tst_discriminant(a*(x^3) + b*(x^2) + c*(x^2) + d,
                     -4*(b^3)*d - 12*(b^2)*c*d - 12*b*(c^2)*d - 4*(c^3)*d - 27*(a^2)*(d^2));
    tst_discriminant(a*(x^3) + b*(x^2) + c*(x^2) + d,
                     -4*(b^3)*d - 12*(b^2)*c*d - 12*b*(c^2)*d - 4*(c^3)*d - 27*(a^2)*(d^2));
    tst_discriminant(a*(x^3) + (b^2)*d*(x^2) + c*(x^2) + d,
                     -4*(b^6)*(d^4) - 12*(b^4)*c*(d^3) - 12*(b^2)*(c^2)*(d^2) - 4*(c^3)*d - 27*(a^2)*(d^2));
    tst_discriminant(a*(x^4) + b*(x^2) + c,
                     16*a*(b^4)*c - 128*(a^2)*(b^2)*(c^2) + 256*(a^3)*(c^3));
    polynomial_ref one(m);
    one = m.mk_const(rational(1));
    tst_discriminant(x, one);
    tst_discriminant(3*x, one);
    polynomial_ref zero(m);
    zero = m.mk_zero();
    tst_discriminant(one, zero);
    tst_discriminant(a*(x^7) + b,
                     -823543*(a^6)*(b^6));
    tst_discriminant(((a^2)+(b^2)+c)*(x^4) + (d + a*b)*x + a,
                     -27*(a^8)*(b^4) - 54*(a^6)*(b^6) - 27*(a^4)*(b^8) - 54*(a^6)*(b^4)*c - 54*(a^4)*(b^6)*c -
                     108*(a^7)*(b^3)*d - 216*(a^5)*(b^5)*d - 108*(a^3)*(b^7)*d - 27*(a^4)*(b^4)*(c^2) -
                     216*(a^5)*(b^3)*c*d - 216*(a^3)*(b^5)*c*d - 162*(a^6)*(b^2)*(d^2) - 324*(a^4)*(b^4)*(d^2) -
                     162*(a^2)*(b^6)*(d^2) + 256*(a^9) + 768*(a^7)*(b^2) + 768*(a^5)*(b^4) + 256*(a^3)*(b^6) -
                     108*(a^3)*(b^3)*(c^2)*d - 324*(a^4)*(b^2)*c*(d^2) - 324*(a^2)*(b^4)*c*(d^2) -
                     108*(a^5)*b*(d^3) - 216*(a^3)*(b^3)*(d^3) - 108*a*(b^5)*(d^3) + 768*(a^7)*c +
                     1536*(a^5)*(b^2)*c + 768*(a^3)*(b^4)*c - 162*(a^2)*(b^2)*(c^2)*(d^2) - 216*(a^3)*b*c*(d^3) -
                     216*a*(b^3)*c*(d^3) - 27*(a^4)*(d^4) - 54*(a^2)*(b^2)*(d^4) - 27*(b^4)*(d^4) + 768*(a^5)*(c^2)
                     + 768*(a^3)*(b^2)*(c^2) - 108*a*b*(c^2)*(d^3) - 54*(a^2)*c*(d^4) - 54*(b^2)*c*(d^4) +
                     256*(a^3)*(c^3) - 27*(c^2)*(d^4));
    tst_discriminant((x^5) + a*(x^2) + a,
                     108*(a^6) + 3125*(a^4));
    tst_discriminant((x^5) + (a*b)*(x^2) + a,
                     108*(a^6)*(b^5) + 3125*(a^4));
    tst_discriminant((x^5) + (a*b*c)*(x^2) + a,
                     108*(a^6)*(b^5)*(c^5) + 3125*(a^4));
    tst_discriminant((x^5) + (a*b*c + d)*(x^2) + a,
                     108*(a^6)*(b^5)*(c^5) + 540*(a^5)*(b^4)*(c^4)*d + 1080*(a^4)*(b^3)*(c^3)*(d^2) +
                     1080*(a^3)*(b^2)*(c^2)*(d^3) + 540*(a^2)*b*c*(d^4) + 108*a*(d^5) + 3125*(a^4));
    tst_discriminant((x^4) + a*(x^2) + (a + c)*x + (c^2),
                     16*(a^4)*(c^2) - 128*(a^2)*(c^4) + 256*(c^6) - 4*(a^5) - 8*(a^4)*c + 140*(a^3)*(c^2) +
                     288*(a^2)*(c^3) + 144*a*(c^4) - 27*(a^4) - 108*(a^3)*c - 162*(a^2)*(c^2) - 108*a*(c^3) -
                     27*(c^4));
    tst_discriminant((x^4) + (a + b)*(x^2) + (a + c)*x,
                     -4*(a^5) - 12*(a^4)*b - 12*(a^3)*(b^2) - 4*(a^2)*(b^3) - 8*(a^4)*c - 24*(a^3)*b*c -
                     24*(a^2)*(b^2)*c - 8*a*(b^3)*c - 4*(a^3)*(c^2) - 12*(a^2)*b*(c^2) - 12*a*(b^2)*(c^2) -
                     4*(b^3)*(c^2) - 27*(a^4) - 108*(a^3)*c - 162*(a^2)*(c^2) - 108*a*(c^3) - 27*(c^4));
    tst_discriminant((x^4) + (a + c)*x + (c^2),
                     256*(c^6) - 27*(a^4) - 108*(a^3)*c - 162*(a^2)*(c^2) - 108*a*(c^3) - 27*(c^4)
                     );
    tst_discriminant((x^4) + (a + b)*(x^2) + (a + c)*x + (c^2),
                     16*(a^4)*(c^2) + 64*(a^3)*b*(c^2) + 96*(a^2)*(b^2)*(c^2) + 64*a*(b^3)*(c^2) + 16*(b^4)*(c^2) -
                     128*(a^2)*(c^4) - 256*a*b*(c^4) - 128*(b^2)*(c^4) + 256*(c^6) - 4*(a^5) - 12*(a^4)*b -
                     12*(a^3)*(b^2) - 4*(a^2)*(b^3) - 8*(a^4)*c - 24*(a^3)*b*c - 24*(a^2)*(b^2)*c - 8*a*(b^3)*c
                     + 140*(a^3)*(c^2) + 132*(a^2)*b*(c^2) - 12*a*(b^2)*(c^2) - 4*(b^3)*(c^2) + 288*(a^2)*(c^3) +
                     288*a*b*(c^3) + 144*a*(c^4) + 144*b*(c^4) - 27*(a^4) - 108*(a^3)*c - 162*(a^2)*(c^2) -
                     108*a*(c^3) - 27*(c^4));
    tst_discriminant((a + c)*(x^3) + (a + b)*(x^2) + (a + c)*x + (c^2),
                     -27*(a^2)*(c^4) - 54*a*(c^5) - 27*(c^6) + 14*(a^3)*(c^2) + 6*(a^2)*b*(c^2) -
                     12*a*(b^2)*(c^2) - 4*(b^3)*(c^2) + 36*(a^2)*(c^3) + 36*a*b*(c^3) + 18*a*(c^4) + 18*b*(c^4)
                     - 3*(a^4) + 2*(a^3)*b + (a^2)*(b^2) - 14*(a^3)*c + 4*(a^2)*b*c + 2*a*(b^2)*c -
                     23*(a^2)*(c^2) + 2*a*b*(c^2) + (b^2)*(c^2) - 16*a*(c^3) - 4*(c^4));
    tst_discriminant((a^4) - 2*(a^3) + (a^2) - 3*(b^2)*a + 2*(b^4),
                     max_var(a),
                     2048*(b^12) - 4608*(b^10) + 37*(b^8) + 12*(b^6));
    tst_discriminant((a^4) - 2*(a^3) + (a^2) - 3*(b^2)*a + 2*(b^4),
                     max_var(b),
                     2048*(a^12) - 12288*(a^11) + 26112*(a^10) - 22528*(a^9) + 5664*(a^8) + 960*(a^7) +
                     32*(a^6));
    tst_discriminant((x^4) + a*(x^2) + b*x + c,
                     -4*(a^3)*(b^2) + 16*(a^4)*c - 27*(b^4) + 144*a*(b^2)*c - 128*(a^2)*(c^2) + 256*(c^3));
    tst_discriminant((((a-1)^2) + a*b + ((b-1)^2) - 1)*(x^3) + (a*b)*(x^2) + ((a^2) - (b^2))*x + c*a,
                     -4*(a^8) - 4*(a^7)*b + 9*(a^6)*(b^2) + 12*(a^5)*(b^3) - 2*(a^4)*(b^4) - 12*(a^3)*(b^5) -
                     7*(a^2)*(b^6) + 4*a*(b^7) + 4*(b^8) + 18*(a^6)*b*c + 18*(a^5)*(b^2)*c - 4*(a^4)*(b^3)*c -
                     18*(a^3)*(b^4)*c - 18*(a^2)*(b^5)*c - 27*(a^6)*(c^2) - 54*(a^5)*b*(c^2) - 81*(a^4)*(b^2)*(c^2)
                     - 54*(a^3)*(b^3)*(c^2) - 27*(a^2)*(b^4)*(c^2) + 8*(a^7) + 8*(a^6)*b - 24*(a^5)*(b^2) -
                     24*(a^4)*(b^3) + 24*(a^3)*(b^4) + 24*(a^2)*(b^5) - 8*a*(b^6) - 8*(b^7) - 36*(a^5)*b*c -
                     36*(a^4)*(b^2)*c + 36*(a^3)*(b^3)*c + 36*(a^2)*(b^4)*c + 108*(a^5)*(c^2) + 216*(a^4)*b*(c^2)
                     + 216*(a^3)*(b^2)*(c^2) + 108*(a^2)*(b^3)*(c^2) - 4*(a^6) + 12*(a^4)*(b^2) - 12*(a^2)*(b^4) +
                     4*(b^6) + 18*(a^4)*b*c - 18*(a^2)*(b^3)*c - 162*(a^4)*(c^2) - 270*(a^3)*b*(c^2) -
                     162*(a^2)*(b^2)*(c^2) + 108*(a^3)*(c^2) + 108*(a^2)*b*(c^2) - 27*(a^2)*(c^2));
}

static void tst_resultant(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x, polynomial_ref const & expected) {
    polynomial::manager & m = p.m();
    polynomial_ref r(m);
    std::cout << "----------------\n";
    std::cout << "p: " << p << "\n";
    std::cout << "q: " << q << std::endl;
    r = resultant(p, q, x);
    std::cout << "r: " << r << "\n";
    std::cout << "expected: " << expected << "\n";
    if (degree(p, x) > 0 && degree(q, x) > 0)
        std::cout << "quasi-resultant: " << quasi_resultant(p, q, x) << "\n";
    SASSERT(eq(r, expected));
    m.lex_sort(r);
    std::cout << "r (sorted): " << r << "\n";
}

static void tst_resultant(polynomial_ref const & p, polynomial_ref const & q, polynomial_ref const & expected) {
    tst_resultant(p, q, max_var(p), expected);
}

static void tst_resultant() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref a(m);
    polynomial_ref b(m);
    polynomial_ref c(m);
    polynomial_ref d(m);
    polynomial_ref x(m);
    a = m.mk_polynomial(m.mk_var());
    b = m.mk_polynomial(m.mk_var());
    c = m.mk_polynomial(m.mk_var());
    d = m.mk_polynomial(m.mk_var());
    x = m.mk_polynomial(m.mk_var());

    tst_resultant((((a-1)^2) + a*b + ((b-1)^2) - 1)*(x^3) + (a*b)*(x^2) + ((a^2) - (b^2))*x + c*a,
                  a*b*(x^2) - (a^2) - (b^2),
                  -4*(a^9)*b - (a^10) - 9*(a^8)*(b^2) - 11*(a^7)*(b^3) - 14*(a^6)*(b^4) - 10*(a^5)*(b^5) -
                  10*(a^4)*(b^6) - 3*(a^3)*(b^7) - 5*(a^2)*(b^8) - (b^10) + 2*(a^6)*(b^3)*c + 2*(a^4)*(b^5)*c +
                  (a^5)*(b^3)*(c^2) + 4*(a^9) + 12*(a^8)*b + 24*(a^7)*(b^2) + 32*(a^6)*(b^3) + 40*(a^5)*(b^4) +
                  32*(a^4)*(b^5) + 24*(a^3)*(b^6) + 16*(a^2)*(b^7) + 4*a*(b^8) + 4*(b^9) - 6*(a^8) -
                  12*(a^7)*b - 24*(a^6)*(b^2) - 32*(a^5)*(b^3) - 36*(a^4)*(b^4) - 28*(a^3)*(b^5) -
                  24*(a^2)*(b^6) - 8*a*(b^7) - 6*(b^8) + 4*(a^7) + 4*(a^6)*b + 12*(a^5)*(b^2) + 12*(a^4)*(b^3)
                  + 12*(a^3)*(b^4) + 12*(a^2)*(b^5) + 4*a*(b^6) + 4*(b^7) - (a^6) - 3*(a^4)*(b^2) -
                  3*(a^2)*(b^4) - (b^6));


    tst_resultant(a*(x^5) + b,
                  c*x + d,
                  a*(d^5) - b*(c^5));
    tst_resultant(a*(x^5) + 3*(c + d)*(x^2) + 2*b,
                  c*x + d,
                  -2*b*(c^5) - 3*(c^4)*(d^2) - 3*(c^3)*(d^3) + a*(d^5));
    tst_resultant(c*x + d,
                  a*(x^5) + 3*(c + d)*(x^2) + 2*b,
                  2*b*(c^5) + 3*(c^4)*(d^2) + 3*(c^3)*(d^3) - a*(d^5));
    tst_resultant((x^2) - (a^3)*(x^2) + b + 1,
                  -49*(x^10) + 21*(x^8) + 5*(x^6) - (x^4),
                  (a^18)*(b^4) + 4*(a^18)*(b^3) + 6*(a^18)*(b^2) - 10*(a^15)*(b^5) + 4*(a^18)*b -
                  56*(a^15)*(b^4) + (a^18) - 124*(a^15)*(b^3) - 17*(a^12)*(b^6) - 136*(a^15)*(b^2) -
                  52*(a^12)*(b^5) - 74*(a^15)*b + 10*(a^12)*(b^4) + 308*(a^9)*(b^7) - 16*(a^15) +
                  220*(a^12)*(b^3) + 2224*(a^9)*(b^6) + 335*(a^12)*(b^2) + 6776*(a^9)*(b^5) - 49*(a^6)*(b^8) +
                  208*(a^12)*b + 11280*(a^9)*(b^4) - 1316*(a^6)*(b^7) + 48*(a^12) + 11060*(a^9)*(b^3) -
                  7942*(a^6)*(b^6) - 2058*(a^3)*(b^9) + 6368*(a^9)*(b^2) - 22660*(a^6)*(b^5) -
                  18424*(a^3)*(b^8) + 1984*(a^9)*b - 36785*(a^6)*(b^4) - 72380*(a^3)*(b^7) + 2401*(b^10) +
                  256*(a^9) - 36064*(a^6)*(b^3) - 163592*(a^3)*(b^6) + 26068*(b^9) - 21216*(a^6)*(b^2) -
                  234058*(a^3)*(b^5) + 126518*(b^8) - 6912*(a^6)*b - 219344*(a^3)*(b^4) + 361508*(b^7) -
                  960*(a^6) - 134208*(a^3)*(b^3) + 673537*(b^6) - 51456*(a^3)*(b^2) + 855056*(b^5) -
                  11136*(a^3)*b + 749104*(b^4) - 1024*(a^3) + 447232*(b^3) + 174144*(b^2) + 39936*b + 4096);
    tst_resultant(((a - x)^2) + 2,
                  (x^5) - x - 1,
                  (a^10) + 10*(a^8) + 38*(a^6) - 2*(a^5) + 100*(a^4) + 40*(a^3) + 121*(a^2) - 38*a + 19);
    tst_resultant(c - (((a^3) - 1)*(b^2) - 1),
                  ((a^2) - 2)*(a - 2),
                  max_var(a),
                  -49*(b^6) + 21*(b^4)*c + 21*(b^4) + 5*(b^2)*(c^2) + 10*(b^2)*c - (c^3) + 5*(b^2) - 3*(c^2) - 3*c - 1);
    tst_resultant(-49*(b^6) + 21*(b^4)*c + 21*(b^4) + 5*(b^2)*(c^2) + 10*(b^2)*c - (c^3) + 5*(b^2) - 3*(c^2) - 3*c - 1,
                  (7*(b^4) - 2*(b^2) - 1),
                  max_var(b),
                  117649*(c^12) + 1075648*(c^11) + 1651888*(c^10) - 12293120*(c^9) - 46560192*(c^8)
                  - 9834496*(c^7) + 186855424*(c^6) + 314703872*(c^5) + 157351936*(c^4));
    tst_resultant(144*(b^2) + 96*(a^2)*b + 9*(a^4) + 105*(a^2) + 70*a - 98,
                  a*(b^2) + 6*a*b + (a^3) + 9*a,
                  max_var(b),
                  81*(a^10) + 3330*(a^8) + 1260*(a^7) - 37395*(a^6) - 45780*(a^5) - 32096*(a^4) +
                  167720*(a^3) + 1435204*(a^2));
    tst_resultant(144*(b^2) + 96*(a^2)*b + 9*(a^4) + 105*(a^2) + 70*a - 98,
                  a*(b^2) + 6*a*b + (a^3) + 9*a,
                  max_var(a),
                  11664*(b^10) + 31104*(b^9) - 119394*(b^8) - 1550448*(b^7) - 2167524*(b^6) +
                  7622712*(b^5) + 46082070*(b^4) + 46959720*(b^3) - 9774152*(b^2) - 35007168*b -
                  13984208);
    polynomial_ref n1(m);
    polynomial_ref n2(m);
    polynomial_ref one(m);
    n1 = m.mk_const(rational(10));
    n2 = m.mk_const(rational(100));
    one = m.mk_const(rational(1));
    tst_resultant(n1, (x^2) + 2*x + 1, max_var(x), n2);
    tst_resultant(n1, 2*x + 1, max_var(x), n1);
    tst_resultant(n1, n2, 0, one);
    tst_resultant((x^2) + 2*x + 1, n1, max_var(x), n2);
    tst_resultant(2*x + 1, n1, max_var(x), n1);
    tst_resultant((x^2) + 8*x + 1, n1, max_var(x), n2);
}

static void tst_compose() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    p = (x0^3) - x0 + 3;
    std::cout << "p: " << p << "\np(x - y): " << compose_x_minus_y(p, 1)
              << "\np(x + y): " << compose_x_plus_y(p, 1) << "\np(x - x): " << compose_x_minus_y(p, 0) << "\np(x + x): " << compose_x_plus_y(p, 0) << "\n";
    SASSERT(eq(compose_x_minus_y(p, 1), (x0^3) - 3*(x0^2)*x1 + 3*x0*(x1^2) - (x1^3) - x0 + x1 + 3));
    SASSERT(eq(compose_x_plus_y(p, 1), (x0^3) + 3*(x0^2)*x1 + 3*x0*(x1^2) + (x1^3) - x0 - x1 + 3));
}

void tst_prem() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    polynomial_ref y(m);
    x = m.mk_polynomial(m.mk_var());
    y = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (x^2) - 2;
    q = y*(x^3);
    std::cout << "p: " << p << "\n";
    std::cout << "q: " << q << "\n";
    // unsigned d;
    std::cout << "srem: " << exact_pseudo_remainder(q, p, 0) << "\n";
}

void tst_sqrt() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    polynomial_ref y(m);
    x = m.mk_polynomial(m.mk_var());
    y = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    p = (4*x*y + 3*(x^2)*y + (y^2) + 3)^4;
    polynomial_ref q(m);
    VERIFY(sqrt(p, q));
    SASSERT(eq(p, q*q));
    std::cout << "p: " << p << "\n";
    std::cout << "q: " << q << "\n";
    p = p - 1;
    SASSERT(!sqrt(p, q));
}

static void tst_content(polynomial_ref const & p, polynomial::var x, polynomial_ref const & expected) {
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    std::cout << "content(p): " << content(p, x) << std::endl;
    std::cout << "expected: " << expected << std::endl;
    SASSERT(eq(content(p, x), expected));
}

static void tst_primitive(polynomial_ref const & p, polynomial::var x, polynomial_ref const & expected) {
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    std::cout << "primitive(p): " << primitive(p, x) << std::endl;
    std::cout << "expected: " << expected << std::endl;
    SASSERT(eq(primitive(p, x), expected));
}

static void tst_gcd(polynomial_ref const & p, polynomial_ref const & q, polynomial_ref const & expected) {
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    std::cout << "q: " << q << std::endl;
    polynomial_ref r(p.m());
    r = gcd(p, q);
    std::cout << "gcd(p, q): " << r << std::endl;
    std::cout << "expected: " << expected << std::endl;
    SASSERT(eq(r, expected));
}

static void tst_gcd() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    polynomial_ref three(m);
    three = m.mk_const(mpz(3));

    std::cout << "tst_gcd\n======================\n";

    tst_gcd(((x0^2) + x0*x1 + 1)*(x2*x2 + x3 + 2)*(x3*x1 + 2)*(x3*x1*x1 + x1*x2 + 1),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1)*(x3*x1 + x1*x2 + 17),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1));

    tst_gcd((-1)*((x0^2) + x0*x1 + 1)*(x2*x2 + x3 + 2)*(x3*x1 + 2)*(x3*x1*x1 + x1*x2 + 1),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1)*(x3*x1 + x1*x2 + 17),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1));

    tst_gcd(((x0^2) + x0*x1 + 1)*(x2*x2 + x3 + 2)*(x3*x1 + 2)*(x3*x1*x1 + x1*x2 + 1),
            (-1)*((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1)*(x3*x1 + x1*x2 + 17),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1));

    tst_gcd((-1)*((x0^2) + x0*x1 + 1)*(x2*x2 + x3 + 2)*(x3*x1 + 2)*(x3*x1*x1 + x1*x2 + 1),
            (-1)*((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1)*(x3*x1 + x1*x2 + 17),
            ((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1));

    tst_gcd(21*(x0 + 1), 6*x0^2, three);
    tst_content(x0*x1 + x0, 1, x0);
    tst_primitive(x0*x1 + x0, 1, x1 + 1);
    tst_primitive((x1^2) + x0*x1 + x0, 1, (x1^2) + x0*x1 + x0);
    tst_primitive((x0 + 1)*(2*x1) + 1, 1, (x0 + 1)*(2*x1) + 1);
    tst_primitive((x0 + 1)*(2*x1) + (x0^2)*(x0 + 1), 1, 2*x1 + (x0^2));
    tst_primitive((x0 + 1)*(x2 + 1)*(x2^2)*(x0 + 1)*(x1^2) + (x0 + 1)*(x2^2)*x1 + (x0+1)*(x0+1), 1,
                  (x2 + 1)*(x2^2)*(x0 + 1)*(x1^2) + (x2^2)*x1 + (x0+1));
    tst_primitive((x0 + (x3^2))*(x2 + x3 + 1)*(x2^2)*(x1^2) +
                  (x0 + (x3^2))*(x2 + x3 + 1)*x1 +
                  (x0 + (x3^2))*(x2 + x3 + 1)*(x3^2),
                  1,
                  (x2^2)*(x1^2) + x1 + (x3^2));
    tst_content((x0 + (x3^2))*(x2 + x3 + 1)*(x2^2)*(x1^2) +
                (x0 + (x3^2))*(x2 + x3 + 1)*x1 +
                (x0 + (x3^2))*(x2 + x3 + 1)*(x3^2),
                1,
                (x0 + (x3^2))*(x2 + x3 + 1));
    tst_primitive(4*(x0 + (x3^2))*(x2 + x3 + 1)*(x2^2)*(x1^2) +
                  2*(x0 + (x3^2))*(x2 + x3 + 1)*x1 +
                  4*(x0 + (x3^2))*(x2 + x3 + 1)*(x3^2),
                  1,
                  2*(x2^2)*(x1^2) + x1 + 2*(x3^2));
    tst_gcd(63*((x0^2) + x0*x1 + 1)*(x2*x2 + x3 + 2)*(x3*x1 + 2)*(x3*x1*x1 + x1*x2 + 1),
            14*((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1)*(x3*x1 + x1*x2 + 17),
            7*((x0^2) + x0*x1 + 1)*(x3*x1*x1 + x1*x2 + 1));
}

static void tst_psc(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x, polynomial_ref const & first, polynomial_ref const & second) {
    polynomial::manager & m = p.m();
    polynomial_ref_vector S(m);
    std::cout << "---------" << std::endl;
    std::cout << "p: " << p << std::endl;
    std::cout << "q: " << q << std::endl;
    m.psc_chain(p, q, x, S);
    unsigned sz = S.size();
    for (unsigned i = 0; i < sz; i++) {
        std::cout << "S_" << i << ": " << polynomial_ref(S.get(i), m) << std::endl;
    }
    if (sz > 0) {
        SASSERT(m.eq(S.get(0), first) || m.eq(S.get(0), neg(first)));
    }
    if (sz > 1) {
        SASSERT(m.eq(S.get(1), second) || m.eq(S.get(1), neg(second)));
    }
    if (sz > 0) {
        polynomial_ref Res(m);
        Res = resultant(p, q, x);
        SASSERT(m.eq(Res, S.get(0)) || m.eq(S.get(0), neg(Res)));
    }
}

#if 0
static void tst_psc_perf(polynomial_ref const & p, polynomial_ref const & q, polynomial::var x) {
    polynomial::manager & m = p.m();
    polynomial_ref_vector S(m);
    std::cout << "---------" << std::endl;
    std::cout << "p: " << p << std::endl;
    std::cout << "q: " << q << std::endl;
    m.psc_chain(p, q, x, S);
    unsigned sz = S.size();
    for (unsigned i = 0; i < sz; i++) {
        std::cout << "S_" << i << ": " << m.size(S.get(i)) << std::endl; // polynomial_ref(S.get(i), m) << std::endl;
    }
}
#endif

static void tst_psc() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    polynomial_ref x4(m);
    polynomial_ref x5(m), x6(m), x7(m), x8(m), x9(m), x10(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());
    x6 = m.mk_polynomial(m.mk_var());
    x7 = m.mk_polynomial(m.mk_var());
    x8 = m.mk_polynomial(m.mk_var());
    x9 = m.mk_polynomial(m.mk_var());
    x10 = m.mk_polynomial(m.mk_var());
    tst_psc(x0*(x1^2) + (x0 + 1)*x1 + 2, x0*x1 + 3, 1,
            6*x0 - (x0^2), x0);
    tst_psc(x0*(x1^4) + (x0 + 1)*(x1^3) + 2, x0*(x1^3) + 3, 1,
            72*(x0^3) - (x0^4) - 27*(x0^2) - 27*(x0), 9*(x0^3));
    polynomial_ref & a = x0;
    polynomial_ref & b = x1;
    polynomial_ref & c = x2;
    polynomial_ref & d = x3;
    polynomial_ref & e = x4;
    polynomial_ref & f = x5;
    polynomial_ref & x = x9;
    tst_psc((x^4) + a*(x^2) + b*x + c, 4*(x^3) + 2*a*x + b, 9,
            16*(a^4)*c - 4*(a^3)*(b^2) - 128*(a^2)*(c^2) + 144*a*(b^2)*c - 27*(b^4) + 256*(c^3), 8*(a^3) - 32*a*c + 36*(b^2));
    polynomial_ref & y = x10;

    tst_psc(((y^2) + 6)*(x - 1) - y*((x^2) + 1), ((x^2) + 6)*(y - 1) - x*((y^2) + 1), 10,
            2*(x^6) - 22*(x^5) + 102*(x^4) - 274*(x^3) + 488*(x^2) - 552*x + 288,
            5*x - (x^2) - 6
            );

    tst_psc(((y^3) + 6)*(x - 1) - y*((x^3) + 1), ((x^3) + 6)*(y - 1) - x*((y^3) + 1), 10,
            3*(x^11) - 3*(x^10) - 37*(x^9) + 99*(x^8) + 51*(x^7) - 621*(x^6) + 1089*(x^5) - 39*(x^4) - 3106*(x^3) + 5868*(x^2) - 4968*x + 1728,
            (x^6) - 10*(x^4) + 12*(x^3) + 25*(x^2) - 60*x + 36);

    polynomial_ref p = (x^6) + a * (x^3) + b;
    polynomial_ref q = (x^6) + c * (x^3) + d;

    tst_psc(p, q, 9,
            (b^6) - 3*a*(b^5)*c + 3*(a^2)*(b^4)*(c^2) + 3*(b^5)*(c^2) - (a^3)*(b^3)*(c^3) -
            6*a*(b^4)*(c^3) + 3*(a^2)*(b^3)*(c^4) + 3*(b^4)*(c^4) - 3*a*(b^3)*(c^5) + (b^3)*(c^6) +
            3*(a^2)*(b^4)*d - 6*(b^5)*d - 6*(a^3)*(b^3)*c*d + 9*a*(b^4)*c*d +
            3*(a^4)*(b^2)*(c^2)*d + 6*(a^2)*(b^3)*(c^2)*d - 12*(b^4)*(c^2)*d - 9*(a^3)*(b^2)*(c^3)*d +
            6*a*(b^3)*(c^3)*d + 9*(a^2)*(b^2)*(c^4)*d - 6*(b^3)*(c^4)*d - 3*a*(b^2)*(c^5)*d +
            3*(a^4)*(b^2)*(d^2) - 12*(a^2)*(b^3)*(d^2) + 15*(b^4)*(d^2) - 3*(a^5)*b*c*(d^2) +
            6*(a^3)*(b^2)*c*(d^2) - 6*a*(b^3)*c*(d^2) + 9*(a^4)*b*(c^2)*(d^2) -
            18*(a^2)*(b^2)*(c^2)*(d^2) + 18*(b^3)*(c^2)*(d^2) - 9*(a^3)*b*(c^3)*(d^2) +
            6*a*(b^2)*(c^3)*(d^2) + 3*(a^2)*b*(c^4)*(d^2) + 3*(b^2)*(c^4)*(d^2) + (a^6)*(d^3) -
            6*(a^4)*b*(d^3) + 18*(a^2)*(b^2)*(d^3) - 20*(b^3)*(d^3) - 3*(a^5)*c*(d^3) +
            6*(a^3)*b*c*(d^3) - 6*a*(b^2)*c*(d^3) + 3*(a^4)*(c^2)*(d^3) + 6*(a^2)*b*(c^2)*(d^3) -
            12*(b^2)*(c^2)*(d^3) - (a^3)*(c^3)*(d^3) - 6*a*b*(c^3)*(d^3) + 3*(a^4)*(d^4) -
            12*(a^2)*b*(d^4) + 15*(b^2)*(d^4) - 6*(a^3)*c*(d^4) + 9*a*b*c*(d^4) +
            3*(a^2)*(c^2)*(d^4) + 3*b*(c^2)*(d^4) + 3*(a^2)*(d^5) - 6*b*(d^5) -
            3*a*c*(d^5) + (d^6),
            3*(a^2)*c - (a^3) - 3*a*(c^2) + (c^3)
            );


    tst_psc(x,
            a * x + b * c + d - e,
            9,
            b*c + d - e, a);

    polynomial_ref zero(m);
    zero = m.mk_zero();

    tst_psc( a*d*x + a*c*f + a*e - b*a,
             d*x + c*f + e - b,
             9, zero, zero);


#if 0
    tst_psc_perf((x^7) + a*(x^3) + b*(x^2) + c*x + d,
                 (x^7) + e*(x^3) + f*(x^2) + g*x + h,
                 9);

    tst_psc_perf((x^15) + a * (x^10) + b,
                 (x^15) + c * (x^10) + d,
                 9);

    tst_psc_perf((y^5) + a * (y^4) + b * (y^3) + c * (y^2) + d * y + e,
                 (y^5) + f * (y^4) + g * (y^3) + h * (y^2) + i * y + x,
                 10);
#endif
}

static void tst_vars(polynomial_ref const & p, unsigned sz, polynomial::var * xs) {
    polynomial::var_vector r;
    p.m().vars(p, r);
    std::cout << "---------------\n";
    std::cout << "p: " << p << "\nvars: ";
    for (unsigned i = 0; i < r.size(); i++) {
        std::cout << r[i] << " ";
    }
    std::cout << std::endl;
    SASSERT(r.size() == sz);
    std::sort(r.begin(), r.end());
    std::sort(xs, xs + sz);
    for (unsigned i = 0; i < r.size(); i++) {
        SASSERT(r[i] == xs[i]);
    }
}

static void tst_vars() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    polynomial_ref x4(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    polynomial::var s023[3] = {0, 2, 3};
    polynomial::var s14[2] = {1, 4};
    polynomial::var s012[3] = {0, 1, 2};
    polynomial::var s3[1] = {3};
    polynomial::var s01234[5] = {0, 1, 2, 3, 4};

    tst_vars((x0 + 1)*((x0^2) + (x3^2))*(x2*x3), 3, s023);
    tst_vars((x0 + x2)*((x0^2) + (x3^2))*(x2*x3), 3, s023);
    tst_vars(((x1 + x4 + 1)^5), 2, s14);
    tst_vars(((x1 + x4*x2 + 1)^4) + x0 + (x3^2), 5, s01234);
    tst_vars((x3 + 1)^5, 1, s3);
    tst_vars(x0*x1*x2, 3, s012);
    tst_vars(x0*x1*x2 + 1, 3, s012);
}

static void tst_sqf(polynomial_ref const & p, polynomial_ref const & expected) {
    polynomial_ref r(p.m());
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    r = square_free(p);
    std::cout << "sqf(p): " << r << std::endl;
    std::cout << "expected: " << expected << std::endl;
    SASSERT(is_square_free(r));
    SASSERT(!eq(r, p) || is_square_free(p));
    SASSERT(eq(expected, r));
}

static void tst_sqf() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    tst_sqf(((x0 + x1)^2)*((x0^2) - 3)*((x2*x2 + x3 + 1)^3),
            (x0 + x1)*((x0^2) - 3)*(x2*x2 + x3 + 1));
    tst_sqf((x0 + x1)*(x0 - x1), (x0 + x1)*(x0 - x1));
    tst_sqf(((x0 + x1)^3)*(x0 - x1), (x0 + x1)*(x0 - x1));
    polynomial_ref c1(m);
    c1 = m.mk_const(rational(3));
    tst_sqf(c1, c1);
    polynomial_ref z(m);
    z = m.mk_zero();
    tst_sqf(z, z);
    tst_sqf((x0 + x1 + x2 + x3)^5, (x0 + x1 + x2 + x3));
    tst_sqf(((x0 + x1 + x2 + x3)^5) + 1, ((x0 + x1 + x2 + x3)^5) + 1);
}

static void tst_substitute(polynomial_ref const & p,
                           polynomial::var x1, mpz const & v1,
                           polynomial::var x2, mpz const & v2,
                           polynomial_ref const & expected) {
    polynomial::numeral_manager & nm = p.m().m();
    polynomial::var xs[2] = { x1, x2 };
    scoped_mpz_vector vs(nm);
    vs.push_back(v1);
    vs.push_back(v2);
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    polynomial_ref r(p.m());
    r = p.m().substitute(p, 2, xs, vs.c_ptr());
    std::cout << "r: " << r << std::endl;
    std::cout << "expected: " << expected << std::endl;
    SASSERT(eq(r, expected));
    p.m().lex_sort(r);
    std::cout << "r (sorted): " << r << std::endl;
}

static void tst_substitute() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    tst_substitute(x0 + x1*x0 + x3, 1, mpz(1), 3, mpz(2), 2*x0 + 2);
    tst_substitute((x0^2) + x1*x0 + x3, 0, mpz(2), 3, mpz(2), 2*x1 + 6);
    tst_substitute((x0 + x1 + x2)^3, 0, mpz(2), 2, mpz(3), (x1 + 5)^3);
    tst_substitute(((x0 + x1 + x2)^3) + ((x0*x1 + x3)^2), 0, mpz(2), 2, mpz(3), ((x1 + 5)^3) + ((2*x1 + x3)^2));
    tst_substitute((x0 + x1 + 1)^5, 2, mpz(2), 3, mpz(3), (x0 + x1 + 1)^5);
    polynomial_ref zero(m);
    zero = m.mk_zero();
    tst_substitute(zero, 2, mpz(2), 3, mpz(3), zero);
}

static void tst_qsubstitute(polynomial_ref const & p,
                            unsynch_mpq_manager & qm,
                            polynomial::var x1, rational const & v1,
                            polynomial::var x2, rational const & v2,
                            polynomial_ref const & expected) {
    polynomial::var xs[2] = { x1, x2 };
    scoped_mpq_vector vs(qm);
    vs.push_back(v1.to_mpq());
    vs.push_back(v2.to_mpq());
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    polynomial_ref r(p.m());
    r = p.m().substitute(p, 2, xs, vs.c_ptr());
    std::cout << "r: " << r << std::endl;
    std::cout << "expected (modulo a constant): " << expected << std::endl;
    SASSERT(eq(r, normalize(expected)));
    p.m().lex_sort(r);
    std::cout << "r (sorted): " << r << std::endl;
}

static void tst_qsubstitute() {
    unsynch_mpq_manager qm;
    reslimit rl; polynomial::manager m(rl, qm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    tst_qsubstitute(x0 + x1 + x2, qm, 0, rational(1)/rational(2), 1, rational(3), 2*x2 + 2*3 + 1);
    tst_qsubstitute((x0^2)*x2 + x1 + x2*x0, qm, 0, rational(3)/rational(2), 1, rational(3), 9*x2 + (4*3) + (2*3)*x2);
    tst_qsubstitute(x0*x1*x2*(x3^2) + (x0^3)*x3 + (x1^2)*x0, qm,
                    0, rational(5)/rational(2),
                    1, rational(7)/rational(3),
                    (2*2*3*7*5)*x2*(x3^2) + (5*5*5*3*3)*x3 + (7*7*5*2*2));
    tst_qsubstitute((x2 + x3)^3, qm,
                    0, rational(5)/rational(2),
                    1, rational(7)/rational(3),
                    (x2 + x3)^3);
    tst_qsubstitute((x0 + x1 + x2 + x3)^3, qm,
                    0, rational(5)/rational(2),
                    2, rational(7)/rational(3),
                    (6*x1 + 6*x3 + 15 + 14)^3);
    tst_qsubstitute((x0 + 2*x1 + 11*(x2^2)*x3 + x2 + (x3^2))^3, qm,
                    0, rational(5)/rational(2),
                    3, rational(7)/rational(3),
                    ((2*3*3*2)*x1 + (11*2*3*7)*(x2^2) + (2*3*3)*x2 + (5*9 + 7*7*2))^3);
    polynomial_ref zero(m);
    zero = m.mk_zero();
    tst_qsubstitute(zero, qm,
                    0, rational(5)/rational(2),
                    3, rational(7)/rational(3),
                    zero);
}

void tst_mfact(polynomial_ref const & p, unsigned num_distinct_factors) {
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    polynomial::factors fs(p.m());
    factor(p, fs);
    std::cout << "factors:\n";
    std::cout << p.m().m().to_string(fs.get_constant()) << "\n";
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        std::cout << "*(" << fs[i] << ")^" << fs.get_degree(i) << std::endl;
    }
    SASSERT(fs.distinct_factors() == num_distinct_factors);
    polynomial_ref p2(p.m());
    fs.multiply(p2);
    SASSERT(eq(p, p2));
}

static void tst_mfact() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    polynomial_ref x4(m);
    polynomial_ref x5(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());
    polynomial_ref & x = x0;

    tst_mfact((x0 - (x1^3))*(x0 - ((x2^3) - 2)), 2);
    tst_mfact((((x3^3) + 1)*x0 - (x1^3))*(x0 - ((x2^3) - 2)), 2);
    tst_mfact((((x3^3) + 1)*x0 - (x1^3))*((x3 - 1)*x0 - ((x2^3) - 2)), 2);
    tst_mfact((((x3^3) + 1)*x0 - (x1^3))*((-1)*x0 - ((x2^3) - 2)), 2);
    tst_mfact((-1)*(x0 - (x1^3))*(x0 - ((x2^3) - 2)), 2);
    tst_mfact((-1)*(x0 - (x1^3) + (x1^2) + 2)*(x0 - ((x2^3) - 2)), 2);

    tst_mfact(((x0 - (x1^3))*(x0 - ((x2^3) - 2)))^2, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*(x0 - ((x2^3) - 2)))^2, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((x3 - 1)*x0 - ((x2^3) - 2)))^2, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((-1)*x0 - ((x2^3) - 2)))^2, 2);
    tst_mfact(((-1)*(x0 - (x1^3))*(x0 - ((x2^3) - 2)))^2, 2);
    tst_mfact(((-1)*(x0 - (x1^3) + (x1^2) + 2)*(x0 - ((x2^3) - 2)))^2, 2);

    tst_mfact(((x0 - (x1^3))*(x0 - ((x2^3) - 2)))^3, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*(x0 - ((x2^3) - 2)))^3, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((x3 - 1)*x0 - ((x2^3) - 2)))^3, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((-1)*x0 - ((x2^3) - 2)))^3, 2);
    tst_mfact(((-1)*(x0 - (x1^3))*(x0 - ((x2^3) - 2)))^3, 2);
    tst_mfact(((-1)*(x0 - (x1^3) + (x1^2) + 2)*(x0 - ((x2^3) - 2)))^3, 2);

    tst_mfact(((x0 - (x1^3))*(x0 - ((x2^3) - 2)))^4, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*(x0 - ((x2^3) - 2)))^4, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((x3 - 1)*x0 - ((x2^3) - 2)))^4, 2);
    tst_mfact(((((x3^3) + 1)*x0 - (x1^3))*((-1)*x0 - ((x2^3) - 2)))^4, 2);
    tst_mfact(((-1)*(x0 - (x1^3))*(x0 - ((x2^3) - 2)))^4, 2);
    tst_mfact(((-1)*(x0 - (x1^3) + (x1^2) + 2)*(x0 - ((x2^3) - 2)))^4, 2);

    tst_mfact(((x^5) - (x^2) + 1)*((-1)*x + 1)*((x^2) - 2*x + 3), 3);
    tst_mfact(11*((x^5) - (x^2) + 1)*((-1)*x + 1)*((x^2) - 2*x + 3), 3);
    tst_mfact(11*(7*(x^5) - (x^2) + 1)*((-1)*(x^2) + 1)*((x^2) - 2*x + 3), 4);
    tst_mfact(11*(7*(x^5) - (x^2) + 1)*((-1)*(x^2) + 1)*((x^2) - 2*x + 3)*((x^7) - x +2), 5);
    tst_mfact((7*(x^5) - (x^2) + 1)*((-1)*(x^2) + 1)*((x^2) - 2*x + 3)*((x^7) - x +2)*((x^3) - x + 1), 6);
    tst_mfact((7*(x^5) - (x^2) + 1)*((-1)*(x^2) + 1)*((x^2) - 2*x + 3)*((x^7) - x +2)*((x^3) - x + 1)*((x^7) - (x^5) + (x^3) + (x^2) + x + 3), 7);
    tst_mfact((7*(x^5) - (x^2) + 1)*((-1)*(x^2) + 1)*((x^2) - 2*x + 3)*((x^7) - x +2)*
              ((x^3) - x + 1)*((x^7) - (x^5) + (x^3) + (x^2) + x + 3)*(x - (x^3) + 11)*
              (x - 10)*(x - 9)*(33*x + 12)*((x^5) - x + 1),
              12);
    tst_mfact((x^4) + (x^2) - 20, 3);
    tst_mfact((-11)*((x^5) - (x^2) + 1)*((-1)*x + 1)*((x^2) - 2*x + 3), 3);
    tst_mfact(x0 - 2*(x0^2) + 1, 2);
    tst_mfact((x0 + 1)*(x0 - 1)*(x0 + 2)*(((x1^5) - x1 - 1)^2), 4);
    tst_mfact((x0 + 1)*((x1 + 2)^2), 2);
    tst_mfact(7*(x0 + 1)*((x1 + 2)^2), 2);
    tst_mfact(11*(x0 + 1)*((x1 + 2)^2)*((x1 - x3)^4), 3);
    tst_mfact(11*(x0 + 1)*((x1 + 2)^2)*((x1 - x3)^4)*(((x0*(x2^2) + (x0 + x1)*x2 + x1))^3), 5);
    tst_mfact((11*(x0 + 1)*((x1 + 2)^2))^3, 2);
    tst_mfact((3*(x0 + 1)*(x1 + 2))^3, 2);
    tst_mfact((3*(x0 + 1)*(2*x1 + 2))^3, 2);
    tst_mfact(3*(2*(x0^2) + 4*(x1^2))*x2, 2);
    tst_mfact(13*((x0 - x2)^6)*((x1 - x2)^5)*((x0 - x3)^7), 3);
    tst_mfact((x0+1)^100, 1);
    tst_mfact((x0^70) - 6*(x0^65) - (x0^60) + 60*(x0^55) - 54*(x0^50) - 230*(x0^45) + 274*(x0^40) + 542*(x0^35) - 615*(x0^30) - 1120*(x0^25) + 1500*(x0^20) - 160*(x0^15) - 395*(x0^10) + 76*(x0^5) + 34, 3);
    tst_mfact(((x0^4) - 8*(x0^2)), 2);
    tst_mfact((x0^5) - 2*(x0^3) + x0 - 1, 1);
    tst_mfact( (x0^25) - 4*(x0^21) - 5*(x0^20) + 6*(x0^17) + 11*(x0^16) + 10*(x0^15) - 4*(x0^13) - 7*(x0^12) - 9*(x0^11) - 10*(x0^10) +
               (x0^9) + (x0^8) + (x0^7) + (x0^6) + 3*(x0^5) + x0 - 1, 2);
    tst_mfact( (x0^25) - 10*(x0^21) - 10*(x0^20) - 95*(x0^17) - 470*(x0^16) - 585*(x0^15) - 40*(x0^13) - 1280*(x0^12) - 4190*(x0^11) - 3830*(x0^10) + 400*(x0^9)+ 1760*(x0^8) + 760*(x0^7) - 2280*(x0^6) + 449*(x0^5) + 640*(x0^3) - 640*(x0^2) + 240*x0 - 32, 2);
    tst_mfact( x0^10, 1);
    polynomial_ref c(m);
    c = m.mk_zero();
    tst_mfact(c, 0);
    c = m.mk_const(mpz(3));
    tst_mfact(c, 0);
    tst_mfact(x0, 1);
    tst_mfact(x0 + x1, 1);
    tst_mfact(x0 - x1, 1);
    tst_mfact( (x0^10) - 10*(x0^8) + 38*(x0^6) - 2*(x0^5) - 100*(x0^4) - 40*(x0^3) + 121*(x0^2) - 38*x0 - 17, 1);
    tst_mfact( (x0^50) - 10*(x0^40) + 38*(x0^30) - 2*(x0^25) - 100*(x0^20) - 40*(x0^15) + 121*(x0^10) - 38*(x0^5) - 17, 1);
    polynomial_ref & y = x0;
    tst_mfact(        (((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^10)
                 + 10*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^9)
                 + 35*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^8)
                 + 40*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^7)
                 - 32*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^6)
                 - 82*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^5)
                 - 30*(((y^5)  +  5*(y^4) +  10*(y^3) + 10*(y^2) + 5*y)^4)
                 - 140*(((y^5) + 5*(y^4) +   10*(y^3) + 10*(y^2) + 5*y)^3)
                 - 284*(((y^5) + 5*(y^4) +   10*(y^3) + 10*(y^2) + 5*y)^2)
                 - 168*((y^5)  + 5*(y^4) +   10*(y^3) + 10*(y^2) + 5*y)
                 - 47, 1);
    tst_mfact( (y^4) - 404*(y^2) + 39204, 2);
    tst_mfact( ((y^5) - 15552)*
               ((y^20)- 15708*(y^15) + rational("138771724")*(y^10)- rational("432104148432")*(y^5) + rational("614198284585616")),
               2);
    tst_mfact( (y^25) -
               rational("3125")*(y^21) -
               rational("15630")*(y^20) +
               rational("3888750")*(y^17) +
               rational("38684375")*(y^16) +
               rational("95765635")*(y^15) -
               rational("2489846500")*(y^13) -
               rational("37650481875")*(y^12) -
               rational("190548065625")*(y^11) -
               rational("323785250010")*(y^10) +
               rational("750249453025")*(y^9) +
               rational("14962295699875")*(y^8) +
               rational("111775113235000")*(y^7) +
               rational("370399286731250")*(y^6) +
               rational("362903064503129")*(y^5) -
               rational("2387239013984400")*(y^4) -
               rational("23872390139844000")*(y^3) -
               rational("119361950699220000")*(y^2) -
               rational("298404876748050000")*y -
               rational("298500366308609376"), 2);

    tst_mfact( rational("54")*(y^24) - (y^27) - 324*(y^21) + rational("17496")*(y^18) - 34992*(y^15)+ rational("1889568")*(y^12)- 1259712*(y^9) + rational("68024448")*(y^6), 3);

    tst_mfact( ((y^3)- 432)*(((y^3)+54)^2)*((y^6)+108)*((y^6)+6912)*((y^6)- 324*(y^3)+37044),
               5);

    tst_mfact( ((y^6)- 6*(y^4) - 864*(y^3) + 12*(y^2) - 5184*y + 186616)*
               (((y^6) - 6*(y^4) + 108*(y^3) + 12*(y^2) + 648*y + 2908)^2)*
               ((y^12) - 12*(y^10) + 60*(y^8) + 56*(y^6) + 6720*(y^4) + 12768*(y^2) + 13456)*
               ((y^12) - 12*(y^10) + 60*(y^8) + 13664*(y^6) + 414960*(y^4) + 829248*(y^2) + 47886400)*
               ((y^12) - 12*(y^10) - 648*(y^9)+ 60*(y^8) + 178904*(y^6) + 15552*(y^5) + 1593024*(y^4) - 24045984*(y^3) + 5704800*(y^2) - 143995968*y + 1372010896),
               5);

    {
        polynomial_ref q1(m);
        polynomial_ref q2(m);
        polynomial_ref q3(m);
        polynomial_ref q4(m);
        polynomial_ref q5(m);
        polynomial_ref p(m);
        q1 = (x0^3) - 2;
        q2 = (x1^3) - 2;
        q3 = (x2^3) - 2;
        q4 = (x3^2) - 2;
        q5 = (x4^7) - x4 + 3;
        p = x5 - x0 - 2*x1 /* - 3*x2 - x3 */ + x4;
        p = resultant(p, q1, 0);
        std::cout << "finished resultant 1... size: " << size(p) << std::endl;
        p = resultant(p, q2, 1);
        std::cout << "finished resultant 2... size: " << size(p) << std::endl;
        // p = resultant(p, q3, 2);
        std::cout << "finished resultant 3... size: " << size(p) << std::endl;
        // p = resultant(p, q4, 3);
        std::cout << "finished resultant 4... size: " << size(p) << std::endl;
        p = resultant(p, q5, 4);
        tst_mfact(p, 2);
    }
}


static void tst_zp() {
    unsynch_mpz_manager    z;
    reslimit rl; polynomial::manager    pm(rl, z);

    polynomial_ref x(pm);
    polynomial_ref y(pm);
    x = pm.mk_polynomial(pm.mk_var());
    y = pm.mk_polynomial(pm.mk_var());

    polynomial_ref p(pm);
    polynomial_ref q(pm);
    p = (x^4) + 2*(x^3) + 2*(x^2) + x;
    q = (x^3) + x + 1;
    std::cout << "p: " << p << "\n";
    std::cout << "q: " << q << "\n";
    std::cout << "gcd: " << gcd(p, q) << "\n";

    {
        polynomial::scoped_set_zp setZ3(pm, 3);
        polynomial_ref p3(pm);
        polynomial_ref q3(pm);
        p3 = normalize(p);
        q3 = normalize(q);
        std::cout << "p[Z_3]: " << p3 << "\n";
        std::cout << "q[Z_3]: " << q3 << "\n";
        std::cout << "gcd[Z_3]: " << gcd(p3, q3) << "\n";
    }

    std::cout << "back into Z[x,y]\ngcd: " << gcd(p, q) << "\n";

    p = 5*(x^2)*(y^2) + 3*(x^3) + 7*(y^3) + 3;
    {
        polynomial::scoped_set_zp setZ11(pm, 11);
        polynomial_ref p11(pm);

        std::cout << "---------------\n";
        p11 = normalize(p);
        std::cout << "p[Z_11]: " << p11 << "\n";
        p11 = pm.mk_glex_monic(p11);
        std::cout << "monic p[Z_11]: " << p11 << "\n";
    }
    std::cout << "back into Z[x,y]\n";
    std::cout << "p: " << p << "\n";
    std::cout << "gcd: " << gcd(p, q) << "\n";
}

static void tst_translate(polynomial_ref const & p, polynomial::var x0, int v0, polynomial::var x1, int v1, polynomial::var x2, int v2,
                          polynomial_ref const & expected) {
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    polynomial::var xs[3] = { x0, x1, x2 };
    mpz vs[3] = { mpz(v0), mpz(v1), mpz(v2) };
    polynomial_ref r(p.m());
    p.m().translate(p, 3, xs, vs, r);
    std::cout << "r: " << r << std::endl;
    SASSERT(eq(expected, r));
}

static void tst_translate() {
    unsynch_mpq_manager qm;
    reslimit rl; polynomial::manager m(rl, qm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    tst_translate((x0^2) + x1 + 1, 0, 1, 1, 2, 3, 0,
                  (x0^2) + 2*x0 + x1 + 4
                  );
    tst_translate(x3 + 1, 0, 1, 1, 2, 2, 3,
                  x3 + 1
                  );
    tst_translate(x3 + 1, 0, 1, 1, 2, 3, 0,
                  x3 + 1
                  );
    tst_translate(x3 + 1, 0, 1, 1, 2, 3, 10,
                  x3 + 11
                  );
    tst_translate((x0^3)*(x1^2) + (x0^2)*(x1^3) + 10, 0, -3, 1, -2, 3, 0,
                  (x0^3)*(x1^2) + (x0^2)*(x1^3) - 4*(x0^3)*x1 - 15*(x0^2)*(x1^2) - 6*x0*(x1^3) + 4*(x0^3) +
                  48*(x0^2)*x1 + 63*x0*(x1^2) + 9*(x1^3) - 44*(x0^2) - 180*x0*x1 - 81*(x1^2) +
                  156*x0 + 216*x1 - 170
                  );
}

#if 0
static void tst_p25() {
    unsynch_mpq_manager qm;
    reslimit rl; polynomial::manager m(rl, qm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    polynomial_ref x4(m);
    polynomial_ref x5(m);
    polynomial_ref x6(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());
    x6 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    p = (x0 + x1 + x2 + x3 + x4 + x5 + x6)^25;
    std::cout << "size(p): " << size(p) << "\n";
}
#endif

static void tst_mm() {
    unsynch_mpq_manager qm;
    // pm1 and pm2 share the same monomial manager
    reslimit rl;
    polynomial::manager * pm1_ptr = alloc(polynomial::manager, rl, qm);
    polynomial::manager & pm1 = *pm1_ptr;
    polynomial::manager pm2(rl, qm, &pm1.mm());
    polynomial::manager pm3(rl, qm); // pm3 has its own manager
    polynomial_ref p2(pm2);
    {
        polynomial_ref x0(pm1);
        polynomial_ref x1(pm1);
        polynomial_ref x2(pm1);
        x0 = pm1.mk_polynomial(pm1.mk_var());
        x1 = pm1.mk_polynomial(pm1.mk_var());
        x2 = pm1.mk_polynomial(pm1.mk_var());
        polynomial_ref p1(pm1);
        p1 = (x0 + x1 + x2)^2;

        std::cout << "p1: " << p1 << "\n";
        p2 = convert(pm1, p1, pm2);
        std::cout << "p2: " << p2 << "\n";
        SASSERT(pm1.get_monomial(p1, 0) == pm2.get_monomial(p2, 0));

        polynomial_ref p3(pm3);
        p3 = convert(pm1, p1, pm3);
        SASSERT(pm1.get_monomial(p1, 0) != pm3.get_monomial(p3, 0));
    }
    dealloc(pm1_ptr);
    // p2 is still ok
    std::cout << "p2: " << p2 << "\n";
}

static void tst_eval(polynomial_ref const & p, polynomial::var x0, rational v0, polynomial::var x1, rational v1, polynomial::var x2, rational v2,
                     rational expected) {
    TRACE("eval_bug", tout << "tst_eval, " << p << "\n";);
    std::cout << "p: " << p << "\nx" << x0 << " -> " << v0 << "\nx" << x1 << " -> " << v1 << "\nx" << x2 << " -> " << v2 << "\n";
    unsynch_mpq_manager qm;
    polynomial::simple_var2value<unsynch_mpq_manager> x2v(qm);
    x2v.push_back(x0, v0.to_mpq());
    x2v.push_back(x1, v1.to_mpq());
    x2v.push_back(x2, v2.to_mpq());
    scoped_mpq r(qm);
    p.m().eval(p, x2v, r);
    std::cout << "r: " << r << "\nexpected: " << expected << "\n";
    scoped_mpq ex(qm);
    qm.set(ex, expected.to_mpq());
    SASSERT(qm.eq(r, ex));
}

static void tst_eval() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    tst_eval(2000*x1 - x0, 0, rational(1), 1, rational(2), 2, rational(3), rational(3999));
    tst_eval(x0 + 1, 0, rational(1), 1, rational(2), 2, rational(3), rational(2));
    tst_eval((x0^3) + x0 + 1, 0, rational(2), 1, rational(2), 2, rational(3), rational(11));
    tst_eval((x0^3) - 2*x0 + 1, 0, rational(2), 1, rational(2), 2, rational(3), rational(5));
    tst_eval((x0^3) - 2*x0 + 1, 0, rational(-2), 1, rational(2), 2, rational(3), rational(-3));
    tst_eval((x0^4) - 2*x0 + x1 + 1, 0, rational(-2), 1, rational(10), 2, rational(3), rational(31));
    tst_eval((x0^4) - 2*x0 + ((x0^3) + 1)*x1 + 1, 0, rational(-2), 1, rational(10), 2, rational(3), rational(-49));
    tst_eval(((x0^4) - 2*x0)*(x1^2) + ((x0^3) + 1)*x1 + (x0^2) + 1, 0, rational(-2), 1, rational(10), 2, rational(3), rational(1935));
    tst_eval(((x0^4) - 2*x0)*(x1^2)*(x2^3) + ((x0^3) + 1)*x1 + (x0^2) + 1, 0, rational(-2), 1, rational(10), 2, rational(0), rational(-65));
    tst_eval(((x0^4) - 2*x0)*((x1^2) + 1)*(x2^3) + ((x0^3) + 1)*x1 + (x0^2) + 1, 0, rational(-2), 1, rational(10), 2, rational(1, 2), rational(375, 2));
    tst_eval(x0*x1*x2, 0, rational(2), 1, rational(3), 2, rational(1), rational(6));
    tst_eval(x0*x1*x2 + 1, 0, rational(2), 1, rational(3), 2, rational(1), rational(7));
    polynomial_ref one(m);
    one = x0 - x0 + 1;
    tst_eval(one, 0, rational(2), 1, rational(3), 2, rational(1), rational(1));
    tst_eval(x0*(x1^2)*x2 + 1, 0, rational(2), 1, rational(3), 2, rational(1), rational(19));
    tst_eval(x0*(x1^2)*x2 + x1 + 1, 0, rational(2), 1, rational(3), 2, rational(1), rational(22));
    tst_eval(x0*(x1^2)*x2 + x1 + 1 + (x2^2)*(2*x1 - 1), 0, rational(2), 1, rational(3), 2, rational(1), rational(27));
    tst_eval((x0^5) + 1, 0, rational(2), 1, rational(3), 2, rational(1), rational(33));
    tst_eval((x0^5) + x0*x1 + 1, 0, rational(2), 1, rational(1), 2, rational(5), rational(35));
    tst_eval((x1^5) + x0*x1 + 1, 0, rational(2), 1, rational(1), 2, rational(5), rational(4));
    tst_eval((x1^5) + x0*(x1^2) + 1, 0, rational(2), 1, rational(-2), 2, rational(5), rational(-23));
}

static void tst_mk_unique() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    polynomial::cache uniq(m);
    polynomial_ref p(m);
    polynomial_ref q(m);
    polynomial_ref r(m);

    p = (x0^3) + (x2^5) + x0*x1 + x0*x1*x1 + 3*x0*x0 + 5;
    q = x0*x1*x1 + (x0^3) + 3*x0*x0 + (x2^5) + 5 + x0*x1;
    r = x0*x1*x1 + (x0^3) + 3*x0*x0 + (x2^5) + 6 + x0*x1;
    std::cout << "p: " << p << "\n";
    std::cout << "q: " << q << "\n";
    std::cout << "r: " << r << "\n";
     SASSERT(m.eq(p, q));
    SASSERT(!m.eq(p, r));
    SASSERT(p.get() != q.get());
    q = uniq.mk_unique(q);
    p = uniq.mk_unique(p);
    r = uniq.mk_unique(r);
    std::cout << "after mk_unique\np: " << p << "\n";
    std::cout << "q: " << q << "\n";
    std::cout << "r: " << r << "\n";
    SASSERT(m.eq(p, q));
    SASSERT(!m.eq(r, q));
    SASSERT(p.get() == q.get());
}

struct dummy_del_eh : public polynomial::manager::del_eh {
    unsigned m_counter;
    dummy_del_eh():m_counter(0) {}
    virtual void operator()(polynomial::polynomial * p) {
        m_counter++;
    }
};

static void tst_del_eh() {
    dummy_del_eh eh1;
    dummy_del_eh eh2;

    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());

    m.add_del_eh(&eh1);
    x1 = 0;
    SASSERT(eh1.m_counter == 1);

    m.add_del_eh(&eh2);
    x1 = m.mk_polynomial(m.mk_var());
    x1 = 0;
    SASSERT(eh1.m_counter == 2);
    SASSERT(eh2.m_counter == 1);
    m.remove_del_eh(&eh1);
    x0 = 0;
    x1 = m.mk_polynomial(m.mk_var());
    x1 = 0;
    SASSERT(eh1.m_counter == 2);
    SASSERT(eh2.m_counter == 3);
    m.remove_del_eh(&eh2);
    x1 = m.mk_polynomial(m.mk_var());
    x1 = 0;
    SASSERT(eh1.m_counter == 2);
    SASSERT(eh2.m_counter == 3);
}

static void tst_const_coeff() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());

    scoped_mpz c(nm);

    polynomial_ref p(m);

    p = (x0^2)*x1 + 3*x0 + x1;
    SASSERT(!m.const_coeff(p, 0, 2, c));
    SASSERT(m.const_coeff(p, 0, 1, c) && c == 3);
    SASSERT(!m.const_coeff(p, 0, 0, c));

    p = (x0^2)*x1 + 3*x0 + x1 + 1;
    SASSERT(!m.const_coeff(p, 0, 2, c));
    SASSERT(m.const_coeff(p, 0, 1, c) && c == 3);
    SASSERT(!m.const_coeff(p, 0, 0, c));

    p = (x0^2)*x1 + 3*x0 + 1;
    SASSERT(!m.const_coeff(p, 0, 2, c));
    SASSERT(m.const_coeff(p, 0, 1, c) && c == 3);
    SASSERT(m.const_coeff(p, 0, 0, c) && c == 1);

    p = x1 + 3*x0 + 1;
    SASSERT(m.const_coeff(p, 0, 2, c) && c == 0);
    SASSERT(m.const_coeff(p, 0, 1, c) && c == 3);
    SASSERT(!m.const_coeff(p, 0, 0, c));

    p = 5*(x0^2) + 3*x0 + 7;
    SASSERT(m.const_coeff(p, 0, 5, c) && c == 0);
    SASSERT(m.const_coeff(p, 0, 2, c) && c == 5);
    SASSERT(m.const_coeff(p, 0, 1, c) && c == 3);
    SASSERT(m.const_coeff(p, 0, 0, c) && c == 7);

    p = 5*(x0^2) + 3*x0;
    SASSERT(m.const_coeff(p, 0, 0, c) && c == 0);

    p = - x0*x1 - x1 + 1;
    SASSERT(!m.const_coeff(p, 0, 1, c));
}

static void tst_gcd2() {
    // enable_trace("mgcd");
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    polynomial_ref x1(m);
    polynomial_ref x2(m);
    polynomial_ref x3(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref one(m);
    one = m.mk_const(mpz(1));

    tst_gcd(one, one, one);

    tst_gcd((5*x0 + 3*x1)*(x1 + 2)*(x2 + 3),
            (10*x0 + 6*x1)*(x1 + 2)*(x2 + 5),
            (5*x0 + 3*x1)*(x1 + 2));

    tst_gcd((x0 + 1)*(x1 + 2)*(x2 + 3),
            (x0 + 1)*(x1 + 2)*(x2 + 5),
            (x0 + 1)*(x1 + 2));

    tst_gcd(((x1^2) + 2*(x2^2) + 3*(x3^3))*(x1 + x2 + x3 + 1),
            ((x1^2) + 2*(x2^2) + 3*(x3^3))*(x1 + x2 + x3 + 2),
            ((x1^2) + 2*(x2^2) + 3*(x3^3)));

    tst_gcd(5*(x1^3) + 11 + 7*(x0^2),
            5*(x1^3) + 13 + 7*(x0^2),
            one);

    tst_gcd((5*3*(x1^2) + 5*6*(x2^2) + 5*21*(x3^3))*(5*(x1^3) + 7*(x0^2) + 11),
            (7*3*(x1^2) + 7*6*(x2^2) + 7*21*(x3^3))*(5*(x1^3) + 7*(x0^2) + 13),
            (3*(x1^2) + 6*(x2^2) + 21*(x3^3)));

    tst_gcd((x2^6)*(x3^6) - 4*(x2^3)*(x3^6) + 2*(x2^6)*(x3^3) - 8*(x2^3)*(x3^3) + 4*(x1^3)*(x2^3)*(x3^3) - 8*(x1^3)*(x3^3) +
            4*(x3^6) + 8*(x3^3) + (x2^6) - 4*(x2^3) + 4*(x1^3)*(x2^3) - 8*(x1^3) + 4 + (x1^6),
            (-2)*(x2^3)*(x3^6) - 4*(x2^3)*(x3^3) + 4*(x3^6) + 8*(x3^3) - 2*(x1^3)*(x3^3) - 2*(x2^3) + 4 - 2*(x1^3),
            one);

    tst_gcd((x1^2) - 2*x0 + 1 + (x0^2) + x0*x1 - 2*x1,
            x0*x1,
            one);

    tst_gcd((5*3*(x1^2) + 5*6*(x2^2) + 5*21*(x3^3))*(x1 + x2 + x3 + 1)*(5*(x1^3) + 7*(x0^2) + 11),
            (7*3*(x1^2) + 7*6*(x2^2) + 7*21*(x3^3))*(x1 + x2 + x3 + 2)*(5*(x1^3) + 7*(x0^2) + 13),
            (3*(x1^2) + 6*(x2^2) + 21*(x3^3)));

    p = 169*(x1^12)*(x2^16) - 468*x0*(x1^11)*(x2^16) + 428*(x0^2)*(x1^10)*(x2^16) - 92*(x0^3)*(x1^9)*(x2^16) - 82*(x0^4)*(x1^8)*(x2^16) + 52*(x0^5)*(x1^7)*(x2^16) - 4*(x0^6)*(x1^6)*(x2^16) - 4*(x0^7)*(x1^5)*(x2^16) + (x0^8)*(x1^4)*(x2^16) - 581*(x1^14)*(x2^14) + 1828*x0*(x1^13)*(x2^14) - 2452*(x0^2)*(x1^12)*(x2^14) + 548*(x0^3)*(x1^11)*(x2^14) + 1002*(x0^4)*(x1^10)*(x2^14) - 756*(x0^5)*(x1^9)*(x2^14) + 124*(x0^6)*(x1^8)*(x2^14) + 44*(x0^7)*(x1^7)*(x2^14) - 13*(x0^8)*(x1^6)*(x2^14) + 895*(x1^16)*(x2^12) - 1556*x0*(x1^15)*(x2^12) + 2864*(x0^2)*(x1^14)*(x2^12);
    tst_gcd(p, derivative(p, 2), (x1^4)*(x2^11));

    tst_gcd((11*5*3)*((x0^2) + 1)*(x1 + 3),
            (11*5*7)*((x0^2) + 1)*(x1 + 5),
            (11*5)*((x0^2) + 1));

    p = (x0^4)*(x3^8) - 2*(x0^4)*(x3^7) - 2*(x0^3)*(x2^3)*(x3^7) + 4*(x0^3)*(x3^7) + 2*(x0^4)*(x3^5) - 4*(x0^4)*(x3^4) - 4*(x0^3)*(x2^3)*(x3^4) + 8*(x0^3)*(x3^4) - 2*(x0^3)*(x1^3)*(x3^5) + 4*(x0^3)*(x1^3)*(x3^4) + 4*(x0^2)*(x1^3)*(x2^3)*(x3^4) - 8*(x0^2)*(x1^3)*(x3^4) + (x0^4)*(x3^6) + 2*(x0^3)*(x2^3)*(x3^6) - 4*(x0^3)*(x3^6) + 2*(x0^4)*(x3^3) + 4*(x0^3)*(x2^3)*(x3^3) - 8*(x0^3)*(x3^3) - 2*(x0^3)*(x1^3)*(x3^3) - 4*(x0^2)*(x1^3)*(x2^3)*(x3^3) + 8*(x0^2)*(x1^3)*(x3^3) + (x0^2)*(x2^6)*(x3^6) - 4*(x0^2)*(x2^3)*(x3^6) + 2*(x0^2)*(x2^6)*(x3^3) - 8*(x0^2)*(x2^3)*(x3^3) - 2*x0*(x1^3)*(x2^6)*(x3^3) + 8*x0*(x1^3)*(x2^3)*(x3^3) + 4*(x0^2)*(x3^6) + 8*(x0^2)*(x3^3) - 8*x0*(x1^3)*(x3^3) + (x0^4)*(x3^2) - 2*(x0^4)*x3 - 2*(x0^3)*(x2^3)*x3 + 4*(x0^3)*x3 - 2*(x0^3)*(x1^3)*(x3^2) + 4*(x0^3)*(x1^3)*x3 + 4*(x0^2)*(x1^3)*(x2^3)*x3 - 8*(x0^2)*(x1^3)*x3 + (x0^4) + 2*(x0^3)*(x2^3) - 4*(x0^3) - 2*(x0^3)*(x1^3) - 4*(x0^2)*(x1^3)*(x2^3) + 8*(x0^2)*(x1^3) + (x0^2)*(x2^6) - 4*(x0^2)*(x2^3) - 2*x0*(x1^3)*(x2^6) + 8*x0*(x1^3)*(x2^3) + 4*(x0^2) - 8*x0*(x1^3) + (x0^2)*(x1^6)*(x3^2) - 2*(x0^2)*(x1^6)*x3 - 2*x0*(x1^6)*(x2^3)*x3 + 4*x0*(x1^6)*x3 + (x0^2)*(x1^6) + 2*x0*(x1^6)*(x2^3) - 4*x0*(x1^6) + (x1^6)*(x2^6) - 4*(x1^6)*(x2^3) + 4*(x1^6);

    // polynomial_ref p1(m);
    // p1 = derivative(p, 0);
    // polynomial_ref g(m);
    // for (unsigned i = 0; i < 50; i++)
    //    g = gcd(p, p1);
    // return;

    tst_gcd(p, derivative(p, 1),
            x0*(x2^6)*(x3^3) - (x1^3)*(x2^6) - 2*(x0^2)*(x2^3)*(x3^4) + 2*x0*(x1^3)*(x2^3)*x3 + 2*(x0^2)*(x2^3)*(x3^3) + (x0^3)*(x3^5) - 2*x0*(x1^3)*(x2^3) + x0*(x2^6) - (x0^2)*(x1^3)*(x3^2) - 4*x0*(x2^3)*(x3^3) - 2*(x0^3)*(x3^4) + 4*(x1^3)*(x2^3) + 2*(x0^2)*(x1^3)*x3 - 2*(x0^2)*(x2^3)*x3 + (x0^3)*(x3^3) + 4*(x0^2)*(x3^4) - (x0^2)*(x1^3) + 2*(x0^2)*(x2^3) - 4*x0*(x1^3)*x3 + (x0^3)*(x3^2) - 4*(x0^2)*(x3^3) + 4*x0*(x1^3) - 4*x0*(x2^3) - 2*(x0^3)*x3 + 4*x0*(x3^3) + (x0^3) - 4*(x1^3) + 4*(x0^2)*x3 - 4*(x0^2) + 4*x0
            );

    tst_gcd(p, derivative(p, 0),
            neg((-1)*x0*(x2^3)*(x3^3) + (x1^3)*(x2^3) + (x0^2)*(x3^4) - x0*(x1^3)*x3 - (x0^2)*(x3^3) + x0*(x1^3) - x0*(x2^3) + 2*x0*(x3^3) - 2*(x1^3) + (x0^2)*x3 - (x0^2) + 2*x0));

    tst_gcd(p, derivative(p, 2),
            neg((-1)*(x0^2)*(x2^3)*(x3^6) + 2*x0*(x1^3)*(x2^3)*(x3^3) + (x0^3)*(x3^7) - (x1^6)*(x2^3) - 2*(x0^2)*(x1^3)*(x3^4) - (x0^3)*(x3^6) + x0*(x1^6)*x3 + 2*(x0^2)*(x1^3)*(x3^3) - 2*(x0^2)*(x2^3)*(x3^3) + 2*(x0^2)*(x3^6) - x0*(x1^6) + 2*x0*(x1^3)*(x2^3) - 4*x0*(x1^3)*(x3^3) + 2*(x0^3)*(x3^4) + 2*(x1^6) - 2*(x0^2)*(x1^3)*x3 - 2*(x0^3)*(x3^3) + 2*(x0^2)*(x1^3) - (x0^2)*(x2^3) + 4*(x0^2)*(x3^3) - 4*x0*(x1^3) + (x0^3)*x3 - (x0^3) + 2*(x0^2))
            );

    tst_gcd(((11*5*3)*(x0^2) + 1)*(x1 + 3),
            ((11*5*3)*(x0^2) + 1)*(x1 + 5),
            ((11*5*3)*(x0^2) + 1));

    return;
    p = 169*(x1^12)*(x2^16) - 468*x0*(x1^11)*(x2^16) + 428*(x0^2)*(x1^10)*(x2^16) - 92*(x0^3)*(x1^9)*(x2^16) - 82*(x0^4)*(x1^8)*(x2^16) + 52*(x0^5)*(x1^7)*(x2^16) - 4*(x0^6)*(x1^6)*(x2^16) - 4*(x0^7)*(x1^5)*(x2^16) + (x0^8)*(x1^4)*(x2^16) - 581*(x1^14)*(x2^14) + 1828*x0*(x1^13)*(x2^14) - 2452*(x0^2)*(x1^12)*(x2^14) + 548*(x0^3)*(x1^11)*(x2^14) + 1002*(x0^4)*(x1^10)*(x2^14) - 756*(x0^5)*(x1^9)*(x2^14) + 124*(x0^6)*(x1^8)*(x2^14) + 44*(x0^7)*(x1^7)*(x2^14) - 13*(x0^8)*(x1^6)*(x2^14) + 895*(x1^16)*(x2^12) - 1556*x0*(x1^15)*(x2^12) + 2864*(x0^2)*(x1^14)*(x2^12) + 520*(x0^3)*(x1^13)*(x2^12) - 5402*(x0^4)*(x1^12)*(x2^12) + 3592*(x0^5)*(x1^11)*(x2^12) - 156*(x0^6)*(x1^10)*(x2^12) - 680*(x0^7)*(x1^9)*(x2^12) + 171*(x0^8)*(x1^8)*(x2^12) + 12*(x0^9)*(x1^7)*(x2^12) - 4*(x0^10)*(x1^6)*(x2^12) - 957*(x1^18)*(x2^10) - 1132*x0*(x1^17)*(x2^10) + 206*(x0^2)*(x1^16)*(x2^10) + 588*(x0^3)*(x1^15)*(x2^10) + 6861*(x0^4)*(x1^14)*(x2^10) - 5016*(x0^5)*(x1^13)*(x2^10) - 2756*(x0^6)*(x1^12)*(x2^10) + 3952*(x0^7)*(x1^11)*(x2^10) - 1143*(x0^8)*(x1^10)*(x2^10) - 124*(x0^9)*(x1^9)*(x2^10) + 30*(x0^10)*(x1^8)*(x2^10) + 4*(x0^11)*(x1^7)*(x2^10) - (x0^12)*(x1^6)*(x2^10) + 1404*(x1^20)*(x2^8) + 684*x0*(x1^19)*(x2^8) - 1224*(x0^2)*(x1^18)*(x2^8) - 4412*(x0^3)*(x1^17)*(x2^8) - 1442*(x0^4)*(x1^16)*(x2^8) + 4164*(x0^5)*(x1^15)*(x2^8) + 4116*(x0^6)*(x1^14)*(x2^8) - 5308*(x0^7)*(x1^13)*(x2^8) + 392*(x0^8)*(x1^12)*(x2^8) + 1600*(x0^9)*(x1^11)*(x2^8) - 468*(x0^10)*(x1^10)*(x2^8) - 24*(x0^11)*(x1^9)*(x2^8) + 6*(x0^12)*(x1^8)*(x2^8) - 594*(x1^22)*(x2^6) - 324*x0*(x1^21)*(x2^6) + 1980*(x0^2)*(x1^20)*(x2^6) + 1136*(x0^3)*(x1^19)*(x2^6) + 405*(x0^4)*(x1^18)*(x2^6) - 3916*(x0^5)*(x1^17)*(x2^6) - 396*(x0^6)*(x1^16)*(x2^6) + 1876*(x0^7)*(x1^15)*(x2^6) + 1108*(x0^8)*(x1^14)*(x2^6) - 2064*(x0^9)*(x1^13)*(x2^6) + 248*(x0^10)*(x1^12)*(x2^6) + 380*(x0^11)*(x1^11)*(x2^6) - 95*(x0^12)*(x1^10)*(x2^6) + 81*(x1^24)*(x2^4) + 108*x0*(x1^23)*(x2^4) - 432*(x0^2)*(x1^22)*(x2^4) - 276*(x0^3)*(x1^21)*(x2^4) + 481*(x0^4)*(x1^20)*(x2^4) + 144*(x0^5)*(x1^19)*(x2^4) + 788*(x0^6)*(x1^18)*(x2^4) - 1152*(x0^7)*(x1^17)*(x2^4) + 231*(x0^8)*(x1^16)*(x2^4) + 244*(x0^9)*(x1^15)*(x2^4) + 396*(x0^10)*(x1^14)*(x2^4) - 476*(x0^11)*(x1^13)*(x2^4) + 119*(x0^12)*(x1^12)*(x2^4) + 72*(x0^4)*(x1^22)*(x2^2) - 96*(x0^5)*(x1^21)*(x2^2) - 40*(x0^6)*(x1^20)*(x2^2) - 32*(x0^7)*(x1^19)*(x2^2) + 340*(x0^8)*(x1^18)*(x2^2) - 368*(x0^9)*(x1^17)*(x2^2) + 112*(x0^10)*(x1^16)*(x2^2) + 16*(x0^11)*(x1^15)*(x2^2) - 4*(x0^12)*(x1^14)*(x2^2) + 16*(x0^8)*(x1^20) - 64*(x0^9)*(x1^19) + 96*(x0^10)*(x1^18) - 64*(x0^11)*(x1^17) + 16*(x0^12)*(x1^16);
    polynomial_ref p_prime(m);
    p_prime = derivative(p, 2);
    tst_gcd(p, p_prime, x1^4);
}

#if 0
static void tst_gcd3() {
    enable_trace("polynomial_gcd");
    enable_trace("polynomial_gcd_detail");
    enable_trace("mpzzp");
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (x^8) + (x^6) + (x^4) + (x^3) + (x^2) + 1;
    q = (x^6) + (x^4) + x + 1;
    {
        polynomial::scoped_set_zp setZ2(m, 2);
        std::cout << "Z_p: " << nm.to_string(m.p()) << "\n";
        tst_gcd(normalize(p), normalize(q), x + 1);
    }
    {
        polynomial::scoped_set_zp setZ3(m, 3);
        std::cout << "Z_p: " << nm.to_string(m.p()) << "\n";
        polynomial_ref one(m);
        one = m.mk_const(mpz(1));
        tst_gcd(normalize(p), normalize(q), one);
    }
}

static void tst_gcd4() {
    enable_trace("mgcd");
    // enable_trace("CRA");
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (15*x + 15)*((x + 2)^8)*(10000*x + 1)*(x + 3);
    q = (6*x + 6)*((x + 20)^8)*(10000*x + 3)*(x + 30);
    tst_gcd(p, q, 3*x + 3);
    p = (3*x + 2)*((x + 2)^8)*(10000*x + 1)*(x + 3);
    q = (3*x + 2)*((x + 20)^8)*(10000*x + 3)*(x + 30);
    tst_gcd(p, q, 3*x + 2);
    p = ((3*x + 2)*((x + 2)^8)*(10000*x + 1)*(x + 3))^3;
    q = ((3*x + 2)*((x + 20)^8)*(10000*x + 3)*(x + 30))^3;
    tst_gcd(p, q, (3*x + 2)^3);
    p = ((x + 3)^10)*((x^5) - x - 1)*(x + 1)*(x + 2)*(x + 4)*(10000*x + 33)*(x + 6)*(x + 11)*(x+33)*
        ((x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225)*
        (1000000*x + 1)*(333333333*x + 1)*(77777777*x + 1)*(11111111*x + 1)*(x + 128384747)*(x + 82837437)*(x + 22848481);
    tst_gcd(p, derivative(p, 0), (x + 3)^9);
}
#endif

static void tst_newton_interpolation() {
    // enable_trace("newton");
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    polynomial_ref y(m);
    x = m.mk_polynomial(m.mk_var());
    y = m.mk_polynomial(m.mk_var());
    polynomial_ref p1(m), p2(m), p3(m);
    p1 = (-9)*y - 21;
    p2 = (-3)*y + 20;
    p3 = 5*y - 36;
    scoped_mpz_vector ins(nm);
    ins.push_back(mpz(0)); ins.push_back(mpz(1)); ins.push_back(mpz(2));
    polynomial::polynomial * outs[3] = { p1.get(), p2.get(), p3.get() };
    polynomial_ref r(m);
    {
        polynomial::scoped_set_zp setZ97(m, 97);
        m.newton_interpolation(0, 2, ins.c_ptr(), outs, r);
    }
    std::cout << "interpolation result: " << r << "\n";
    SASSERT(m.eq((x^2)*y + 5*x*y + 41*x - 9*y - 21, r));
}

static void tst_slow_mod_gcd() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m), x1(m), x2(m), x3(m), x4(m), x5(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());
    polynomial_ref p(m), q(m), b(m);
    polynomial_ref p_prime(m);

    p = ((x0^3)*x1*x2*x3*x4*x5 + x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 - 2)^2;
    q = derivative(p, 0);
    tst_gcd(p, q, (x0^3)*x1*x2*x3*x4*x5 + x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 - 2);

    b = (x0^10) + (x1^10) + (x2^10) + (x3^10);
    p = b*(x0 + 1);
    q = b*(x0 + 2);
    tst_gcd(p, q, b);

    return;
    p = (x0^8) *
        (((x0^3)*x1*x2*x3*x4*x5 + x0*(x1^3)*x2*x3*x4*x5 + x0*x1*(x2^3)*x3*x4*x5 + x0*x1*x2*(x3^3)*x4*x5 +
          x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 - 2)^2) *
        (((x0^3)*x1*x2*x3*x4*x5 + x0*(x1^3)*x2*x3*x4*x5 + x0*x1*(x2^3)*x3*x4*x5 + x0*x1*x2*(x3^3)*x4*x5 +
          x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 + 2)^2);
    p_prime = derivative(p, 0);
    tst_gcd(p, p_prime,
            (x0^7) *
            ((x0^3)*x1*x2*x3*x4*x5 + x0*(x1^3)*x2*x3*x4*x5 + x0*x1*(x2^3)*x3*x4*x5 + x0*x1*x2*(x3^3)*x4*x5 +
             x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 - 2) *
            ((x0^3)*x1*x2*x3*x4*x5 + x0*(x1^3)*x2*x3*x4*x5 + x0*x1*(x2^3)*x3*x4*x5 + x0*x1*x2*(x3^3)*x4*x5 +
             x0*x1*x2*x3*(x4^3)*x5 + x0*x1*x2*x3*x4*(x5^3) - x0*x1*x2*x3*x4*x5 + 2));
}

void tst_linear_solver() {
    unsynch_mpq_manager qm;
    scoped_mpq_vector as(qm);
    scoped_mpq b(qm);
    scoped_mpq_vector xs(qm);
    linear_eq_solver<unsynch_mpq_manager> solver(qm);

    solver.resize(3);
    xs.resize(3);

    as.reset();
    as.push_back(mpq(2));  as.push_back(mpq(1));  as.push_back(mpq(-1)); qm.set(b, 8);
    solver.add(0, as.c_ptr(), b);

    as.reset();
    as.push_back(mpq(-3)); as.push_back(mpq(-1)); as.push_back(mpq(2));  qm.set(b, -11);
    solver.add(1, as.c_ptr(), b);

    as.reset();
    as.push_back(mpq(-2)); as.push_back(mpq(1));  as.push_back(mpq(2));  qm.set(b, -3);
    solver.add(2, as.c_ptr(), b);

    VERIFY(solver.solve(xs.c_ptr()));
    SASSERT(qm.eq(xs[0], mpq(2)));
    SASSERT(qm.eq(xs[1], mpq(3)));
    SASSERT(qm.eq(xs[2], mpq(-1)));
}

static void tst_lex(polynomial_ref const & p1, polynomial_ref const & p2, int lex_expected, polynomial::var min, int lex2_expected) {
    polynomial::manager & m = p1.m();
    std::cout << "compare ";
    m.display(std::cout, m.get_monomial(p1, 0));
    std::cout << " ";
    m.display(std::cout, m.get_monomial(p2, 0));
    std::cout << " "; std::cout.flush();
    int r1 = lex_compare(m.get_monomial(p1, 0), m.get_monomial(p2, 0));
    int r2 = lex_compare2(m.get_monomial(p1, 0), m.get_monomial(p2, 0), min);
    SASSERT(r1 == lex_expected);
    SASSERT(r2 == lex2_expected);
    std::cout << r1 << " " << r2 << "\n";
    SASSERT(lex_compare(m.get_monomial(p2, 0), m.get_monomial(p1, 0)) == -r1);
    SASSERT(lex_compare2(m.get_monomial(p2, 0), m.get_monomial(p1, 0), min) == -r2);
}

static void tst_lex() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m), x1(m), x2(m), x3(m), x4(m), x5(m);
    x0 = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());

    polynomial_ref one(m);
    one = m.mk_const(mpz(1));

    tst_lex(x0*x4*x1, (x0^10)*(x1^3), 1, 4, -1);
    tst_lex(x0*x3*(x1^2)*x4, x0*(x3^2)*(x1^2)*x4, -1, 3, -1);
    tst_lex((x0^2)*x3*(x1^2)*x4, x0*(x3^2)*(x1^2)*x4, -1, 3, 1);
    tst_lex(x0*x3*(x1^2)*x4, x0*x3*(x1^2)*x4, 0, 3, 0);
    tst_lex(x0*(x3^2)*(x1^2)*x4, x0*x3*(x1^2)*x4, 1, 3, 1);
    tst_lex((x1^2)*x4, x0*x2*x3*x4*x5, -1, 1, -1);
    tst_lex((x1^2)*x3*x4, x0*x1, 1, 1, 1);
    tst_lex(x1*x3*x4, x2*x3*x4, -1, 2, 1);
    tst_lex(x1*x3*x4, x2*x3*x4, -1, 1, -1);
    tst_lex(x1*x3*x4, x0*x2*x3*x4, -1, 1, -1);
    tst_lex(x3, x4, -1, 1, -1);
    tst_lex(x3, x4, -1, 4, 1);
    tst_lex(x2*x3, x4, -1, 1, -1);
    tst_lex(x2*x3, x4, -1, 4, 1);
    tst_lex(x3, x2*x4, -1, 1, -1);
    tst_lex(x3, x2*x4, -1, 4, 1);
    tst_lex(x3, x2*x4, -1, 4, 1);
    tst_lex(one, x3, -1, 1, -1);
    tst_lex(one, x3, -1, 3, -1);
    tst_lex(x3, one, 1, 3, 1);
    tst_lex(x4*x5, (x4^3)*x5, -1, 4, -1);
}

static void tst_divides() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    x0 = m.mk_polynomial(m.mk_var());
    polynomial_ref q(m);
    polynomial_ref p(m);

    q = 16*(x0^27) - 1984*(x0^26) + 1762*(x0^25) + 17351*(x0^24) - 14165*(x0^23) + 16460*(x0^22) + 2919*(x0^21) - 16823*(x0^20) + 1530*(x0^19) +
        10646*(x0^18) + 19217*(x0^17);
    p = 16*(x0^39) - 3648*(x0^38) + 338136*(x0^37) - 16037936*(x0^36) + 392334357*(x0^35) - rational("3851617443")*(x0^34) -
        rational("14636221526")*(x0^33) + rational("377151717618")*(x0^32) + rational("677140776981")*(x0^31) - rational("4308280094419")*(x0^30) +
        rational("312708087606")*(x0^29) + rational("8205543533730")*(x0^28) + rational("3331586202704")*(x0^27) - rational("15291636627072")*(x0^26) +
        rational("433482645282")*(x0^25) + rational("7397104817486")*(x0^24) + rational("1021197979053")*(x0^23) - rational("1373737505247")*(x0^22) -
        rational("639394669026")*(x0^21) - rational("118513560618")*(x0^20) - rational("10405319535")*(x0^19) - rational("358722675")*(x0^18);
    std::cout << "----------------------\n";
    std::cout << "q: " << q << "\n";
    std::cout << "p: " << p << std::endl;
    std::cout << "divides(q, p): " << m.divides(q, p) << "\n";
}

void tst_polynomial() {
    set_verbosity_level(1000);
    // enable_trace("factor");
    // enable_trace("poly_bug");
    // enable_trace("factor_bug");
    disable_trace("polynomial");
    enable_trace("psc_chain_classic");
    enable_trace("Lazard");
    // enable_trace("eval_bug");
    // enable_trace("mgcd");
    tst_psc();
    return;
    tst_eval();
    tst_divides();
    tst_gcd2();
    tst_slow_mod_gcd();
    tst_gcd();

    tst_lex();
    tst_linear_solver();
    tst_newton_interpolation();
    tst_resultant();
    //
    // tst_gcd4();
    // tst_gcd3();
    tst_zp();
    tst_const_coeff();
    tst_psc();
    tst_del_eh();
    tst_mk_unique();
    tst_qsubstitute();
    tst_substitute();
    tst_discriminant();
    tst_mfact();
    tst_mm();
    // tst_p25();
    // return;
    tst_translate();
    // enable_trace("mpz_gcd");
    tst_vars();
    tst_sqf();
    enable_trace("resultant");
    enable_trace("psc");
    disable_trace("polynomial");
    enable_trace("pseudo_remainder");
    enable_trace("resultant_bug");
    tst_sqrt();
    tst_prem();
    tst_compose();
    tst11();
    tst10();
    tst9();
    tst8();
    tst7();
    tst6();
    tst5();
    tst3();
    tst2();
    tst1();
    tst4();
}
#else
void tst_polynomial() {
  // it takes forever to compiler these regressions using clang++
}
#endif
