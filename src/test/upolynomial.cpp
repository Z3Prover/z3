/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    upolynomial.cpp

Abstract:

    Goodies for creating and handling univariate polynomials.

Author:

    Leonardo (leonardo) 2011-12-01

Notes:

--*/
#include "math/polynomial/upolynomial.h"
#include "util/timeit.h"
#include "util/rlimit.h"

static void tst1() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    upolynomial::manager um(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x - 1)*(x + 1)*(x + 2)*(x + 3)*(x - 3);
    std::cout << "p: " << p << "\n";
    // convert p into an univariate polynomial
    upolynomial::scoped_numeral_vector q(um);
    um.to_numeral_vector(p, q);
    std::cout << "q: "; um.display(std::cout, q); std::cout << "\n";

    std::cout << "degree(q): " << um.degree(q) << "\n";

    // display coefficients of q
    std::cout << "expanded q: ";
    for (unsigned i = 0; i < q.size(); i++)
        std::cout << nm.to_string(q[i]) << " ";
    std::cout << "\n";

    // traverse coefficients of q adding 1
    for (unsigned i = 0; i < q.size(); i++) {
        nm.add(q[i], mpz(1), q[i]);
    }
    // All operations in upolynomial::manager assume the leading coefficient of q is not zero.
    // So, if we perform destructive operations on these coefficients, we must execute the "trim" operation
    // before invoking another operation of upolynomial::manager
    um.trim(q);

    // q after adding 1 to all coefficients
    std::cout << "new q: "; um.display(std::cout, q); std::cout << "\n";

    // q^2
    um.mul(q.size(), q.c_ptr(), q.size(), q.c_ptr(), q);
    std::cout << "new q^2: "; um.display(std::cout, q); std::cout << "\n";

    // using pw for (q^2)^3
    um.pw(q.size(), q.c_ptr(), 3, q);
    std::cout << "new (q^2)^3: "; um.display(std::cout, q); std::cout << "\n";
}

static void tst_isolate_roots(polynomial_ref const & p, unsigned prec, mpbq_manager & bqm, mpbq_vector & roots, mpbq_vector & lowers, mpbq_vector & uppers) {
    reslimit rl;
    upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector q(um);
    um.to_numeral_vector(p, q);
    std::cout << "isolating roots of: "; um.display(std::cout, q); std::cout << "\n";
    {
        timeit timer(true, "isolate time");
        um.isolate_roots(q.size(), q.c_ptr(), bqm, roots, lowers, uppers);
    }

    upolynomial::scoped_upolynomial_sequence sseq(um), fseq(um);
    {
        timeit timer(true, "sturm time");
        um.sturm_seq(q.size(), q.c_ptr(), sseq);
        // um.display(std::cout, sseq); std::cout << "\n";
    }

    // Fourier sequence is sensitive to repeated roots... we remove them by taking the square free component.
    upolynomial::scoped_numeral_vector q_sqf(um);
    {
        timeit timer(true, "sqf time");
        um.square_free(q.size(), q.c_ptr(), q_sqf);
        std::cout << "square free part: "; um.display(std::cout, q_sqf); std::cout << "\n";
    }

    {
        timeit timer(true, "fourier time");
        um.fourier_seq(q_sqf.size(), q_sqf.c_ptr(), fseq);
    }

    // um.display(std::cout, fseq);

    std::cout << "num. roots: " << roots.size() + lowers.size() << "\n";
    std::cout << "sign var(-oo): " << um.sign_variations_at_minus_inf(sseq) << "\n";
    std::cout << "sign var(+oo): " << um.sign_variations_at_plus_inf(sseq) << "\n";
    ENSURE(roots.size() + lowers.size() == um.sign_variations_at_minus_inf(sseq) - um.sign_variations_at_plus_inf(sseq));
    std::cout << "roots:";
    for (unsigned i = 0; i < roots.size(); i++) {
        ENSURE(um.eval_sign_at(q.size(), q.c_ptr(), roots[i]) == 0);
        std::cout << " "; bqm.display_decimal(std::cout, roots[i], prec);
    }
    {
        timeit timer(true, "interval check");
        std::cout << "\n";
        std::cout << "intervals:";
        for (unsigned i = 0; i < lowers.size(); i++) {
            std::cout << " (";
            bqm.display_decimal(std::cout, lowers[i], prec);
            std::cout << ", ";
            bqm.display_decimal(std::cout, uppers[i], prec);
            std::cout << ")";
            // Check interval with Sturm sequence. Small detail: Sturm sequence is for close intervals.
            ENSURE(um.eval_sign_at(q.size(), q.c_ptr(), lowers[i]) == 0 ||
                    um.eval_sign_at(q.size(), q.c_ptr(), uppers[i]) == 0 ||
                    um.sign_variations_at(sseq, lowers[i]) - um.sign_variations_at(sseq, uppers[i]) == 1);
            // Fourier sequence may also be used to check if the interval is isolating
            TRACE("upolynomial",
                  tout << "lowers[i]: " << bqm.to_string(lowers[i]) << "\n";
                  tout << "uppers[i]: " << bqm.to_string(uppers[i]) << "\n";
                  tout << "fourier lower: " << um.sign_variations_at(fseq, lowers[i]) << "\n";
                  tout << "fourier upper: " << um.sign_variations_at(fseq, uppers[i]) << "\n";);
            unsigned fsv_lower = um.sign_variations_at(fseq, lowers[i]);
            unsigned fsv_upper = um.sign_variations_at(fseq, uppers[i]);
            VERIFY(um.eval_sign_at(q.size(), q.c_ptr(), lowers[i]) == 0 ||
                   um.eval_sign_at(q.size(), q.c_ptr(), uppers[i]) == 0 ||
                    // fsv_lower - fsv_upper is an upper bound for the number of roots in the interval
                    // fsv_upper - fsv_upper - num_roots is even
                    // Recall that num_roots == 1 in the interval.
                   (fsv_lower - fsv_upper >= 1 && (fsv_lower - fsv_upper - 1) % 2 == 0));
            
            // Double checking using Descartes bounds for the interval
            // Must use square free component.
            unsigned dab = um.descartes_bound_a_b(q_sqf.size(), q_sqf.c_ptr(), bqm, lowers[i], uppers[i]);
            TRACE("upolynomial", tout << "Descartes bound: " << dab << "\n";);
            VERIFY(dab == 1);
        }
    }
    std::cout << "\n";
}

static void tst_isolate_roots(polynomial_ref const & p, unsigned prec = 5) {
    mpbq_manager bqm(p.m().m());
    scoped_mpbq_vector roots(bqm);
    scoped_mpbq_vector lowers(bqm);
    scoped_mpbq_vector uppers(bqm);
    tst_isolate_roots(p, prec, bqm, roots, lowers, uppers);
}

static void check_roots(mpbq_vector const & roots, mpbq_vector const & lowers, mpbq_vector const & uppers, unsigned expected_sz, rational const * expected_roots) {
    ENSURE(expected_sz == roots.size() + lowers.size());
    svector<bool> visited;
    visited.resize(expected_sz, false);
    for (unsigned i = 0; i < expected_sz; i++) {
        rational const & r = expected_roots[i];
        bool found = false;
        for (unsigned j = 0; j < roots.size(); j++) {
            if (to_rational(roots[j]) == r) {
                ENSURE(!visited[j]);
                VERIFY(!found);
                found = true;
                visited[j] = true;
            }
        }
        for (unsigned j = 0; j < lowers.size(); j++) {
            unsigned j_prime = j + roots.size();
            if (to_rational(lowers[j]) < r && r < to_rational(uppers[j])) {
                VERIFY(!found);
                ENSURE(!visited[j_prime]);
                found = true;
                visited[j_prime] = true;
            }
        }
        ENSURE(found);
    }
}

static void tst_isolate_roots(polynomial_ref const & p, unsigned expected_sz, rational const * expected_roots, unsigned prec = 5) {
    mpbq_manager bqm(p.m().m());
    scoped_mpbq_vector roots(bqm);
    scoped_mpbq_vector lowers(bqm);
    scoped_mpbq_vector uppers(bqm);
    tst_isolate_roots(p, prec, bqm, roots, lowers, uppers);
    check_roots(roots, lowers, uppers, expected_sz, expected_roots);
}

static void tst_isolate_roots() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x-1)*(x-2);
    {
        rational ex[2] = { rational(1), rational(2) };
        tst_isolate_roots(p, 2, ex);
    }
    p = (x-1)*(x-1)*x*x*x;
    {
        rational ex[2] = { rational(1), rational(0) };
        tst_isolate_roots(p, 2, ex);
    }
    p = (x^5) - x - 1;
    {
        rational ex[1] = { rational(11673039, 10000000) }; // approximated root
        tst_isolate_roots(p, 1, ex);
    }
    p = (x - 1)*(x + 1)*(x + 2)*(x + 3)*((x - 3)^2);
    {
        rational ex[5] = { rational(1), rational(-1), rational(-2), rational(-3), rational(3) };
        tst_isolate_roots(p, 5, ex);
    }
    p = (10000*x - 31)*(10000*x - 32);
    {
        rational ex[2] = { rational(31, 10000), rational(32, 10000) };
        tst_isolate_roots(p, 2, ex, 10);
    }
    p = (10000*x - 31)*(10000*x - 32)*(10000*x - 33);
    {
        rational ex[3] = { rational(31, 10000), rational(32, 10000), rational(33, 10000) };
        tst_isolate_roots(p, 3, ex, 10);
    }
    p = ((x^5) - x - 1)*((x^5) + x - 1)*(1000*x - 1167);
    {
        rational ex[3] = { rational(11673039, 10000000), // approximated
                           rational(75487766, 100000000), // approximated
                           rational(1167, 1000) };
        tst_isolate_roots(p, 3, ex, 10);
    }
    p = (x - 2)*(x - 4)*(x - 8)*(x - 16)*(x - 32)*(x - 64)*(2*x - 1)*(4*x - 1)*(8*x - 1)*(16*x - 1)*(32*x - 1);
    {
        rational ex[11] = { rational(2), rational(4), rational(8), rational(16), rational(32), rational(64),
                            rational(1, 2), rational(1, 4), rational(1, 8), rational(1, 16), rational(1, 32) };
        tst_isolate_roots(p, 11, ex, 10);
    }
    p = ((x^5) - x - 1)*((x^5) + x - 1)*(1000*x - 1167)*((x^5) - x - 1)*((x^5) + x - 1)*(1000*x - 1167);
    {
        rational ex[3] = { rational(11673039, 10000000), // approximated
                           rational(75487766, 100000000), // approximated
                           rational(1167, 1000) };
        tst_isolate_roots(p, 3, ex, 10);
    }
    p = (x^17) + 5*(x^16) + 3*(x^15) + 10*(x^13) + 13*(x^10) + (x^9) + 8*(x^5) + 3*(x^2) + 7;
    {
        rational ex[3] = { rational(-413582, 100000), // approximated
                           rational(-170309, 100000), // approximated
                           rational(-109968, 100000), // approximated
        };
        tst_isolate_roots(p, 3, ex, 10);
    }
    p = ((x^17) + 5*(x^16) + 3*(x^15) + 10*(x^13) + 13*(x^10) + (x^9) + 8*(x^5) + 3*(x^2) + 7)*(((x^5) - x - 1)^2)*(((x^3) - 2)^2);
    {
        rational ex[5] = { rational(-413582, 100000), // approximated
                           rational(-170309, 100000), // approximated
                           rational(-109968, 100000), // approximated
                           rational(11673039, 10000000), // approximated
                           rational(125992, 100000)  // approximated
        };
        tst_isolate_roots(p, 5, ex, 10);
    }
    p = (((x^5) - 1000000000)^3)*((3*x - 10000000)^2)*((10*x - 632)^2);
    {
        rational ex[3] = { rational(630957, 10000), // approximated
                           rational(10000000, 3),
                           rational(632, 10)
        };
        tst_isolate_roots(p, 3, ex, 10);
    }

}

static void tst_remove_one_half() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m), r(m);
    p = 4*(x^3) - 12*(x^2) - x + 3;
    r = 16*(x^2) - 40*x - 24;
    upolynomial::manager um(rl, nm);
    upolynomial::scoped_numeral_vector _p(um), _q(um), _r(um);
    um.to_numeral_vector(p, _p);
    um.to_numeral_vector(r, _r);
    ENSURE(um.has_one_half_root(_p.size(), _p.c_ptr()));
    um.remove_one_half_root(_p.size(), _p.c_ptr(), _q);
    ENSURE(!um.has_one_half_root(_q.size(), _q.c_ptr()));
    std::cout << "_p: "; um.display(std::cout, _p); std::cout << "\n";
    std::cout << "_r: "; um.display(std::cout, _r); std::cout << "\n";
    std::cout << "_q: "; um.display(std::cout, _q); std::cout << "\n";
    ENSURE(um.eq(_q, _r));

    p = (((x^5) - 1000000000)^3)*((3*x - 10000000)^2)*((10*x - 632)^2);
    um.to_numeral_vector(p, _p);
    ENSURE(!um.has_one_half_root(_p.size(), _p.c_ptr()));

    p = (x - 2)*(x - 4)*(x - 8)*(x - 16)*(x - 32)*(x - 64)*(2*x - 1)*(4*x - 1)*(8*x - 1)*(16*x - 1)*(32*x - 1);
    um.to_numeral_vector(p, _p);
    ENSURE(um.has_one_half_root(_p.size(), _p.c_ptr()));
}

template<typename pmanager>
static void tst_gcd(polynomial_ref const & p, polynomial_ref const & q, pmanager & um) {
    typename pmanager::scoped_numeral_vector _p(um.m()), _q(um.m()), _r(um.m());
    um.to_numeral_vector(p, _p);
    um.to_numeral_vector(q, _q);
    std::cout << "_p:  "; um.display(std::cout, _p); std::cout << "\n";
    std::cout << "_q:  "; um.display(std::cout, _q); std::cout << std::endl;
    um.gcd(_p.size(), _p.c_ptr(), _q.size(), _q.c_ptr(), _r);
    std::cout << "gcd: "; um.display(std::cout, _r); std::cout << "\n";
    um.subresultant_gcd(_p.size(), _p.c_ptr(), _q.size(), _q.c_ptr(), _r);
    std::cout << "_p:  "; um.display(std::cout, _p); std::cout << "\n";
    std::cout << "_q:  "; um.display(std::cout, _q); std::cout << "\n";
    std::cout << "subresultant_gcd: "; um.display(std::cout, _r); std::cout << "\n";
}

static void tst_gcd() {
    std::cout << "\n\nTesting GCD\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    polynomial_ref q(m);

    upolynomial::manager um(rl, nm);

    p = 13*((x - 3)^6)*((x - 5)^5)*((x - 11)^7);
    q = derivative(p, 0);
    tst_gcd(p, q, um);

    return;

    p = (x^8) + (x^6) - 3*(x^4) - 3*(x^3) + 8*(x^2) + 2*x - 5;
    q = 3*(x^6) + 5*(x^4) - 4*(x^2) - 9*x + 21;

    tst_gcd(p, q, um);

    p = ((x - 1)^2)*(x - 3)*(x + 2)*((x - 5)^3);
    q = (x + 1)*(x-1)*((x-3)^2)*(x + 3)*(x - 5);
    tst_gcd(p, q, um);
    std::cout << "expected: " << ((x - 1)*(x-3)*(x-5)) << "\n";

}

static void tst_zp() {
    std::cout << "\n\nTesting Z_p\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    polynomial_ref q(m);
    p = (x^4) + 2*(x^3) + 2*(x^2) + x;
    q = (x^3) + x + 1;

    // Computing GCD of p an q in Z[x]
    std::cout << "GCD in Z[x]\n";
    upolynomial::manager um(rl, nm);
    tst_gcd(p, q, um);

    // Computing GCD of p an q in Z_3[x]
    std::cout << "GCD in Z_3[x]\n";
    upolynomial::zp_manager um3(rl, nm);
    um3.set_zp(3);
    tst_gcd(p, q, um3);
}

static void tst_zp2() {
    std::cout << "\n\nTesting Z_p\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref u(m);
    polynomial_ref v(m);
    v = (x^6) + 5*(x^5) + 9*(x^4) + 5*(x^2) + 5*x;
    u = (x^8) + (x^6) + 10*(x^4) + 10*(x^3) + 8*(x^2) + 2*x + 8;

    // Computing GCD of p an q in Z[x]
    std::cout << "GCD in Z[x]\n";
    upolynomial::manager um(rl, nm);
    tst_gcd(u, v, um);

    // Computing GCD of p an q in Z_3[x]
    std::cout << "GCD in Z_13[x]\n";
    upolynomial::zp_manager um13(rl, nm);
    um13.set_zp(13);
    tst_gcd(u, v, um13);
}

static void tst_ext_gcd() {
    std::cout << "\nExtended GCD\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref a(m);
    polynomial_ref b(m);
    a = (x^6) + 5*(x^5) + 9*(x^4) + 5*(x^2) + 5*x;
    b = (x^8) + (x^6) + 10*(x^4) + 10*(x^3) + 8*(x^2) + 2*x + 8;

    // Computing GCD of p an q in Z_3[x]
    std::cout << "GCD in Z_13[x]\n";
    upolynomial::zp_manager um(rl, nm);
    um.set_zp(13);
    mpzzp_manager & z13 = um.m();
    upolynomial::zp_manager::scoped_numeral_vector A(z13), B(z13), U(z13), V(z13), D(z13);
    um.to_numeral_vector(a, A);
    um.to_numeral_vector(b, B);
    um.ext_gcd(A.size(), A.c_ptr(), B.size(), B.c_ptr(), U, V, D);
    std::cout << "A: "; um.display(std::cout, A); std::cout << "\n";
    std::cout << "B: "; um.display(std::cout, B); std::cout << "\n";
    std::cout << "U: "; um.display(std::cout, U); std::cout << "\n";
    std::cout << "V: "; um.display(std::cout, V); std::cout << "\n";
    std::cout << "D: "; um.display(std::cout, D); std::cout << "\n";
}

static void tst_ext_gcd_z7() {
    std::cout << "\nExtended GCD in Z_7\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref a(m);
    polynomial_ref b(m);

    a = (x^3) + 2;
    b = 6*(x^2) + 6;

    // Computing GCD of a and b in Z_3[x]
    // expecting: D = 1, U = 3*x + 6, V = 3*x^2 + 6*x + 4
    std::cout << "GCD in Z_7[x]\n";
    upolynomial::zp_manager um(rl, nm);
    um.set_zp(7);
    mpzzp_manager & z7 = um.m();
    upolynomial::zp_manager::scoped_numeral_vector A(z7), B(z7), U(z7), V(z7), D(z7);
    um.to_numeral_vector(a, A);
    um.to_numeral_vector(b, B);
    um.ext_gcd(A.size(), A.c_ptr(), B.size(), B.c_ptr(), U, V, D);
    std::cout << "A: "; um.display(std::cout, A); std::cout << "\n";
    std::cout << "B: "; um.display(std::cout, B); std::cout << "\n";
    std::cout << "U: "; um.display(std::cout, U); std::cout << "\n";
    std::cout << "V: "; um.display(std::cout, V); std::cout << "\n";
    std::cout << "D: "; um.display(std::cout, D); std::cout << "\n";
}

static void tst_sturm() {
    std::cout << "\nSturm Seq\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = 7*(x^10) + 3*(x^9) + (x^8) + (x^6) + 10*(x^4) + 10*(x^3) + 8*(x^2) + 2*x + 8;
    // p = ((x^17) + 5*(x^16) + 3*(x^15) + 10*(x^13) + 13*(x^10) + (x^9) + 8*(x^5) + 3*(x^2) + 7)*(((x^5) - x - 1)^2)*(((x^3) - 2)^2);
    // p = ((x^17) + 5*(x^16) + 3*(x^15) + 10*(x^13) + 13*(x^10) + (x^9) + 8*(x^5) + 3*(x^2) + 7)*(((x^5) - x - 1))*(((x^3) - 2));

    upolynomial::manager um(rl, nm);
    upolynomial::scoped_numeral_vector _p(um);
    upolynomial::scoped_upolynomial_sequence seq2(um);
    um.to_numeral_vector(p, _p);
    um.sturm_seq(_p.size(), _p.c_ptr(), seq2);
    std::cout << "upolynomial sturm seq...\n";
    um.display(std::cout, seq2);
}


static void tst_refinable(polynomial_ref const & p, mpbq_manager & bqm, mpbq & a, mpbq & b) {
    reslimit rl;
    upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector _p(um);
    um.to_numeral_vector(p, _p);
    std::cout << "before (" << bqm.to_string(a) << ", " << bqm.to_string(b) << ")\n";
    bool r = um.isolating2refinable(_p.size(), _p.c_ptr(), bqm, a, b);
    if (r) {
        std::cout << "new (" << bqm.to_string(a) << ", " << bqm.to_string(b) << ")\n";
        int sign_a = um.eval_sign_at(_p.size(), _p.c_ptr(), a);
        int sign_b = um.eval_sign_at(_p.size(), _p.c_ptr(), b);
        VERIFY(sign_a != 0 && sign_b != 0 && sign_a == -sign_b);
    }
    else {
        std::cout << "new root: " << bqm.to_string(a) << "\n";
        ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), a) == 0);
    }
}

static void tst_refinable() {
    std::cout << "\nRefinable intervals\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x - 1)*(4*x - 11)*(x - 3);
    std::cout << "p: " << p << "\n";
    mpbq_manager bqm(nm);
    mpbq a(1);
    mpbq b(3);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 2);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 5, 1);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);

    p = (x - 1)*(5*x - 11)*(x - 3);
    std::cout << "p: " << p << "\n";
    bqm.set(a, 1);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 2);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 3, 1);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 1);
    bqm.set(b, 5, 1);
    tst_refinable(p, bqm, a, b);
    bqm.set(a, 3, 1);
    bqm.set(b, 5, 1);
    tst_refinable(p, bqm, a, b);

    p = (x - 1)*(x - 2)*(x - 3);
    std::cout << "p: " << p << "\n";
    bqm.set(a, 1);
    bqm.set(b, 3);
    tst_refinable(p, bqm, a, b);

    bqm.del(a); bqm.del(b);
}

static void tst_refine(polynomial_ref const & p, mpbq_manager & bqm, mpbq & a, mpbq & b, unsigned prec_k=100) {
    reslimit rl; upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector _p(um);
    um.to_numeral_vector(p, _p);
    std::cout << "before (" << bqm.to_string(a) << ", " << bqm.to_string(b) << ")\n";
    bool r = um.refine(_p.size(), _p.c_ptr(), bqm, a, b, prec_k);
    if (r) {
        std::cout << "new (" << bqm.to_string(a) << ", " << bqm.to_string(b) << ")\n";
        std::cout << "as decimal: "; bqm.display_decimal(std::cout, a, prec_k); std::cout << "\n";
    }
    else {
        std::cout << "new root: " << bqm.to_string(a) << "\n";
        std::cout << "as decimal: "; bqm.display_decimal(std::cout, a, prec_k); std::cout << "\n";
    }
}

static void tst_refine() {
    std::cout << "\nRefining intervals\n";
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x^5) - x - 1;
    std::cout << "p: " << p << "\n";
    mpbq_manager bqm(nm);
    scoped_mpbq a(bqm), b(bqm);
    a = 1;
    b = 2;
    tst_refine(p, bqm, a, b, 20);

    p = (x^2) - 2;
    std::cout << "p: " << p << "\n";
    a = 1;
    b = 2;
    tst_refine(p, bqm, a, b, 200);
}

static void tst_translate_q() {
    reslimit rl;
    unsynch_mpq_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x-1)*(x-2)*(x-3)*(x-4);
    upolynomial::manager um(rl, nm);
    upolynomial::scoped_numeral_vector _p(um), _q(um);
    um.to_numeral_vector(p, _p);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(1)) == 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(2)) == 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(3)) == 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(4)) == 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(-1)) != 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(5)) != 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(-2)) != 0);
    scoped_mpq c(nm);
    nm.set(c, 1, 3);
    scoped_mpq r1(nm);
    r1 = 1;
    r1 -= c;
    scoped_mpq r2(nm);
    r2 = 3;
    r2 -= c;
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), r1) != 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), r2) != 0);
    std::cout << "p: "; um.display(std::cout, _p); std::cout << "\n";
    um.translate_q(_p.size(), _p.c_ptr(), c, _q);
    std::cout << "q: "; um.display(std::cout, _q); std::cout << "\n";
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(1)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(2)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(3)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(4)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(-1)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(5)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), mpq(-2)) != 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), r1) == 0);
    ENSURE(um.eval_sign_at(_q.size(), _q.c_ptr(), r2) == 0);
    um.p_1_div_x(_p.size(), _p.c_ptr());
    std::cout << "p: "; um.display(std::cout, _p); std::cout << "\n";
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(1)) == 0);
    nm.set(c, 1, 2);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), c) == 0);
    nm.set(c, 1, 3);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), c) == 0);
    nm.set(c, 1, 4);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), c) == 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(2)) != 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(3)) != 0);
    ENSURE(um.eval_sign_at(_p.size(), _p.c_ptr(), mpq(4)) != 0);
}

static void tst_convert_q2bq(unsynch_mpq_manager & m, polynomial_ref const & p, mpq const & a, mpq const & b) {
    reslimit rl;
    upolynomial::manager um(rl, m);
    upolynomial::scoped_numeral_vector _p(um);
    um.to_numeral_vector(p, _p);
    std::cout << "\np: ";
    um.display(std::cout, _p); std::cout << "\n";
    std::cout << "before (" << m.to_string(a) << ", " << m.to_string(b) << ") (";
    m.display_decimal(std::cout, a, 10); std::cout << ", "; m.display_decimal(std::cout, b, 10); std::cout << ")\n";
    mpbq_manager bqm(m);
    scoped_mpbq c(bqm);
    scoped_mpbq d(bqm);
    if (!um.convert_q2bq_interval(_p.size(), _p.c_ptr(), a, b, bqm, c, d)) {
        std::cout << "found root: " << c << "\n";
    }
    else {
        std::cout << "after (" << c << ", " << d << ")" << " (";
        bqm.display_decimal(std::cout, c, 10); std::cout << ", "; bqm.display_decimal(std::cout, d, 10); std::cout << ")\n";
    }
}

static void tst_convert_q2bq() {
    reslimit rl;
    unsynch_mpq_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x-1)*(x-2)*(x-3)*(x-4);
    scoped_mpq a(nm), b(nm);

    nm.set(a, 1, 3);
    nm.set(b, 7, 5);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 1, 2);
    nm.set(b, 7, 5);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 3, 7);
    nm.set(b, 3, 2);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 0);
    nm.set(b, 3, 2);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 0);
    nm.set(b, 23, 21);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 7, 2);
    nm.set(b, 5);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 999,  1000);
    nm.set(b, 1001, 1000);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 9999,  10000);
    nm.set(b, 10001, 10000);
    tst_convert_q2bq(nm, p, a, b);

    nm.set(a, 39999,  10000);
    nm.set(b, 40001,  10000);
    tst_convert_q2bq(nm, p, a, b);
}

static void tst_sturm2() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    polynomial_ref q(m);

    p = (x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225;
    q = ((x^8) - 40*(x^6) + 352*(x^4) - 960*(x^2) + 576)^2;

    upolynomial::manager um(rl, nm);
    upolynomial::scoped_numeral_vector _p(um), _q(um);
    upolynomial::scoped_upolynomial_sequence seq2(um);
    um.to_numeral_vector(p, _p);
    um.to_numeral_vector(q, _q);
    um.sturm_tarski_seq(_p.size(), _p.c_ptr(), _q.size(), _q.c_ptr(), seq2);

    std::cout << "upolynomial sturm seq...\n";
    um.display(std::cout, seq2);
}

#if 0
static void tst_isolate_roots2() {
    polynomial::numeral_manager nm;
    polynomial::manager m(nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (2*x - 1)*(x - 21)*(x + 12)*(x - 19)*(x + 11)*(x + 34)*(x - 9)*(x - 72)*(10000*x - 4999)*((x^5) - x - 1)*((x^2) - 2)*((x^2) - 3)*((x^7) - 3)*((x^101) - 3);
    {
        tst_isolate_roots(p, 10);
    }
}

static void tst_isolate_roots3() {
    polynomial::numeral_manager nm;
    polynomial::manager m(nm);
    polynomial_ref x1(m), x2(m), x3(m), x4(m), x5(m), x6(m), x(m);
    x  = m.mk_polynomial(m.mk_var());
    x1 = m.mk_polynomial(m.mk_var());
    x2 = m.mk_polynomial(m.mk_var());
    x3 = m.mk_polynomial(m.mk_var());
    x4 = m.mk_polynomial(m.mk_var());
    x5 = m.mk_polynomial(m.mk_var());
    x6 = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p1(m);
    polynomial_ref p2(m);
    polynomial_ref p3(m);
    polynomial_ref p4(m);
    polynomial_ref p5(m);
    polynomial_ref p6(m);
    polynomial_ref q(m);
    polynomial_ref r(m);
    p1 = ((x1^2) - 2);
    p2 = ((x2^2) - 3);
    p3 = ((x3^2) - 5);
    p4 = ((x4^2) - 7);
    p5 = ((x5^2) - 11);
    p6 = ((x6^2) - 13);
    q = (x - x1 - x2 - x3 - x4 - x5 - x6);
    r = resultant(resultant(resultant(resultant(resultant(resultant(q, p1, 1), p2, 2), p3, 3), p4, 4), p5, 5), p6, 6);
    std::cout << "r: " << r << "\n";
    {
        timeit timer(true, "isolate");
        tst_isolate_roots(r, 10);
    }
}

static void tst_gcd2() {
    polynomial::numeral_manager nm;
    polynomial::manager m(nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = ((x^1000) - x + 1)^5;

    reslimit rl; upolynomial::manager um(rl, nm);
    upolynomial::scoped_numeral_vector _p(um);
    upolynomial::scoped_numeral_vector _p_sqf(um);
    um.to_numeral_vector(p, _p);
    {
        timeit timer(true, "gcd");
        um.square_free(_p.size(), _p.c_ptr(), _p_sqf);
    }
    um.display(std::cout, _p_sqf.size(), _p_sqf.c_ptr()); std::cout << "\n";
}
#endif

static void tst_isolate_roots5() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    p = (x^70) - 6*(x^65) - (x^60) + 60*(x^55) - 54*(x^50) - 230*(x^45) + 274*(x^40) + 542*(x^35) - 615*(x^30)
        - 1120*(x^25) + 1500*(x^20) - 160*(x^15) - 395*(x^10) + 76*(x^5) + 34;
    {
        tst_isolate_roots(p, 10);
    }
}

static void tst_exact_div(polynomial_ref const & p1, polynomial_ref const & p2, bool expected, polynomial_ref const & expected_q) {
    reslimit rl;
    upolynomial::manager um(rl, p1.m().m());
    upolynomial::scoped_numeral_vector _p1(um), _p2(um), _q(um), _r(um);
    um.to_numeral_vector(p1, _p1);
    um.to_numeral_vector(p2, _p2);
    if (expected)
        um.to_numeral_vector(expected_q, _q);
    std::cout << "------\n";
    std::cout << "p1: "; um.display(std::cout, _p1); std::cout << "\n";
    std::cout << "p2: "; um.display(std::cout, _p2); std::cout << std::endl;
    bool res = um.exact_div(_p1.size(), _p1.c_ptr(), _p2.size(), _p2.c_ptr(), _r);
    if (res) {
        std::cout << "r:  "; um.display(std::cout, _r); std::cout << "\n";
    }
    if (expected) {
        std::cout << "expected:  "; um.display(std::cout, _q); std::cout << "\n";
    }
    std::cout.flush();
    ENSURE(res == expected);
    ENSURE(expected == um.divides(_p1.size(), _p1.c_ptr(), _p2.size(), _p2.c_ptr()));
    ENSURE(!expected || um.eq(_r, _q));
}

static void tst_exact_div() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m);
    x = m.mk_polynomial(m.mk_var());
    // create univariate polynomial using multivariate polynomial package
    polynomial_ref p(m);
    tst_exact_div((x - 1)*(x - 2)*(x - 3), (x-2)*(x-1), true, (x-3));
    tst_exact_div((x - 1)*(2*x - 4)*(x - 3), (x-2)*(x-1), true, (2*x-6));
    tst_exact_div((x - 1)*(2*x - 4)*(x - 3), (x-2)*(x-1)*(x-4), false, x);
    tst_exact_div((x - 3), (x-1), false, x);
    polynomial_ref z(m);
    z = m.mk_const(rational(0));
    tst_exact_div(z, (x-2)*(x-1)*(x-4), true, z);
    tst_exact_div((x-2)*(x-1)*(x-4), z, false, z);
    tst_exact_div(z, z, false, z);
    polynomial_ref two(m);
    two = m.mk_const(rational(2));
    tst_exact_div((2*x - 2), (x-1), true, two);
    tst_exact_div((2*x - 2), (4*x-4), false, two);
    tst_exact_div((6*x - 4), two, true, (3*x - 2));
}

static void tst_fact(polynomial_ref const & p, unsigned num_distinct_factors, upolynomial::factor_params const & params = upolynomial::factor_params()) {
    ENSURE(is_univariate(p));
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    reslimit rl; upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector _p(um);
    upolynomial::factors fs(um);
    um.to_numeral_vector(p, _p);
    um.factor(_p, fs, params);
    std::cout << "factors:\n";
    std::cout << um.m().to_string(fs.get_constant()) << "\n";
    for (unsigned i = 0; i < fs.distinct_factors(); i++) {
        std::cout << "*("; um.display(std::cout, fs[i]); std::cout << ")^" << fs.get_degree(i) << std::endl;
    }
    ENSURE(fs.distinct_factors() == num_distinct_factors);
    upolynomial::scoped_numeral_vector _r(um);
    fs.multiply(_r);
    TRACE("upolynomial", tout << "_r: "; um.display(tout, _r); tout << "\n_p: "; um.display(tout, _p); tout << "\n";);
    ENSURE(um.eq(_p, _r));
}

static void tst_fact() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m);
    x0 = m.mk_polynomial(m.mk_var());
    tst_fact((x0^4) + (x0^2) - 20, 3);
    tst_fact((x0^4) + (x0^2) - 20, 1, upolynomial::factor_params(5, 1, 1000));
    tst_fact((x0^4) + (x0^2) - 20, 3, upolynomial::factor_params(7, 1, 1000));
    tst_fact((x0^70) - 6*(x0^65) - (x0^60) + 60*(x0^55) - 54*(x0^50) - 230*(x0^45) + 274*(x0^40) + 542*(x0^35) - 615*(x0^30) - 1120*(x0^25) + 1500*(x0^20) - 160*(x0^15) - 395*(x0^10) + 76*(x0^5) + 34, 1, upolynomial::factor_params(3, 1, 20));
    tst_fact((x0^70) - 6*(x0^65) - (x0^60) + 60*(x0^55) - 54*(x0^50) - 230*(x0^45) + 274*(x0^40) + 542*(x0^35) - 615*(x0^30) - 1120*(x0^25) + 1500*(x0^20) - 160*(x0^15) - 395*(x0^10) + 76*(x0^5) + 34, 2, upolynomial::factor_params(3, 1, 72));
    tst_fact((x0^70) - 6*(x0^65) - (x0^60) + 60*(x0^55) - 54*(x0^50) - 230*(x0^45) + 274*(x0^40) + 542*(x0^35) - 615*(x0^30) - 1120*(x0^25) + 1500*(x0^20) - 160*(x0^15) - 395*(x0^10) + 76*(x0^5) + 34, 3, upolynomial::factor_params(3, 1, 80));
    tst_fact( (x0^10) - 10*(x0^8) + 38*(x0^6) - 2*(x0^5) - 100*(x0^4) - 40*(x0^3) + 121*(x0^2) - 38*x0 - 17, 1);
    tst_fact( (x0^4) - 404*(x0^2) + 39204, 2);
    tst_fact(((x0^5) - (x0^2) + 1)*((-1)*x0 + 1)*((x0^2) - 2*x0 + 3), 3);
    tst_fact((x0^4) + (x0^2) - 20, 3);
    tst_fact((-11)*((x0^5) - (x0^2) + 1)*((-1)*x0 + 1)*((x0^2) - 2*x0 + 3), 3);
    tst_fact(x0 - 2*(x0^2) + 1, 2);
    tst_fact(13*((x0 - 3)^6)*((x0 - 5)^5)*((x0 - 11)^7), 3);
    tst_fact((x0+1)^30, 1);
    tst_fact((x0^70) - 6*(x0^65) - (x0^60) + 60*(x0^55) - 54*(x0^50) - 230*(x0^45) + 274*(x0^40) + 542*(x0^35) - 615*(x0^30) - 1120*(x0^25) + 1500*(x0^20) - 160*(x0^15) - 395*(x0^10) + 76*(x0^5) + 34, 3);
    tst_fact(((x0^4) - 8*(x0^2)), 2);
    tst_fact((x0^5) - 2*(x0^3) + x0 - 1, 1);
    tst_fact( (x0^25) - 4*(x0^21) - 5*(x0^20) + 6*(x0^17) + 11*(x0^16) + 10*(x0^15) - 4*(x0^13) - 7*(x0^12) - 9*(x0^11) - 10*(x0^10) +
               (x0^9) + (x0^8) + (x0^7) + (x0^6) + 3*(x0^5) + x0 - 1, 2);
    tst_fact( (x0^25) - 10*(x0^21) - 10*(x0^20) - 95*(x0^17) - 470*(x0^16) - 585*(x0^15) - 40*(x0^13) - 1280*(x0^12) - 4190*(x0^11) - 3830*(x0^10) + 400*(x0^9)+ 1760*(x0^8) + 760*(x0^7) - 2280*(x0^6) + 449*(x0^5) + 640*(x0^3) - 640*(x0^2) + 240*x0 - 32, 2);
    tst_fact( x0^10, 1);
    tst_fact( (x0^2) - 1, 2);
    tst_fact( (-2)*(x0^2) + 2, 2);
    polynomial_ref zero(m);
    polynomial_ref three(m);
    zero = m.mk_zero();
    three = m.mk_const(rational(3));
    tst_fact(zero, 0);
    tst_fact(three, 0);
    tst_fact(x0 + 1, 1);
    tst_fact(x0 - 1, 1);
    tst_fact((-1)*x0 - 1, 1);
    tst_fact((-1)*x0 + 1, 1);
    tst_fact( (x0^10) - 10*(x0^8) + 38*(x0^6) - 2*(x0^5) - 100*(x0^4) - 40*(x0^3) + 121*(x0^2) - 38*x0 - 17, 1);
    tst_fact( (x0^50) - 10*(x0^40) + 38*(x0^30) - 2*(x0^25) - 100*(x0^20) - 40*(x0^15) + 121*(x0^10) - 38*(x0^5) - 17, 1);

    tst_fact(        (((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^10)
                 + 10*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^9)
                 + 35*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^8)
                 + 40*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^7)
                 - 32*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^6)
                 - 82*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^5)
                 - 30*(((x0^5)  +  5*(x0^4) +  10*(x0^3) + 10*(x0^2) + 5*x0)^4)
                 - 140*(((x0^5) + 5*(x0^4) +   10*(x0^3) + 10*(x0^2) + 5*x0)^3)
                 - 284*(((x0^5) + 5*(x0^4) +   10*(x0^3) + 10*(x0^2) + 5*x0)^2)
                 - 168*((x0^5)  + 5*(x0^4) +   10*(x0^3) + 10*(x0^2) + 5*x0)
                 - 47, 1);

    tst_fact( (x0^4) - 404*(x0^2) + 39204, 2);
    tst_fact( ((x0^5) - 15552)*
              ((x0^20)- 15708*(x0^15) + rational("138771724")*(x0^10)- rational("432104148432")*(x0^5) + rational("614198284585616")),
              2);
    tst_fact( (x0^25) -
              rational("3125")*(x0^21) -
              rational("15630")*(x0^20) +
              rational("3888750")*(x0^17) +
              rational("38684375")*(x0^16) +
              rational("95765635")*(x0^15) -
              rational("2489846500")*(x0^13) -
              rational("37650481875")*(x0^12) -
              rational("190548065625")*(x0^11) -
              rational("323785250010")*(x0^10) +
              rational("750249453025")*(x0^9) +
              rational("14962295699875")*(x0^8) +
              rational("111775113235000")*(x0^7) +
              rational("370399286731250")*(x0^6) +
              rational("362903064503129")*(x0^5) -
              rational("2387239013984400")*(x0^4) -
              rational("23872390139844000")*(x0^3) -
              rational("119361950699220000")*(x0^2) -
              rational("298404876748050000")*x0 -
              rational("298500366308609376"), 2);

    tst_fact( rational("54")*(x0^24) - (x0^27) - 324*(x0^21) + rational("17496")*(x0^18) - 34992*(x0^15)+ rational("1889568")*(x0^12)- 1259712*(x0^9) + rational("68024448")*(x0^6), 3);

    tst_fact( ((x0^3)- 432)*(((x0^3)+54)^2)*((x0^6)+108)*((x0^6)+6912)*((x0^6)- 324*(x0^3)+37044),
               5);

    tst_fact( ((x0^6)- 6*(x0^4) - 864*(x0^3) + 12*(x0^2) - 5184*x0 + 186616)*
              (((x0^6) - 6*(x0^4) + 108*(x0^3) + 12*(x0^2) + 648*x0 + 2908)^2)*
              ((x0^12) - 12*(x0^10) + 60*(x0^8) + 56*(x0^6) + 6720*(x0^4) + 12768*(x0^2) + 13456)*
              ((x0^12) - 12*(x0^10) + 60*(x0^8) + 13664*(x0^6) + 414960*(x0^4) + 829248*(x0^2) + 47886400)*
              ((x0^12) - 12*(x0^10) - 648*(x0^9)+ 60*(x0^8) + 178904*(x0^6) + 15552*(x0^5) + 1593024*(x0^4) - 24045984*(x0^3) +
               5704800*(x0^2) - 143995968*x0 + 1372010896),
              5);
}

static void tst_rem(polynomial_ref const & p, polynomial_ref const & q, polynomial_ref const & expected) {
    ENSURE(is_univariate(p));
    ENSURE(is_univariate(q));
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    std::cout << "q: " << q << std::endl;
    reslimit rl; upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector _p(um), _q(um), _r(um);
    um.to_numeral_vector(p, _p);
    um.to_numeral_vector(q, _q);
    um.rem(_p.size(), _p.c_ptr(), _q.size(), _q.c_ptr(), _r);
    polynomial_ref r(p.m());
    r = p.m().to_polynomial(_r.size(), _r.c_ptr(), 0);
    std::cout << "r: " << r << std::endl;
    ENSURE(eq(expected, r));
}

static void tst_rem() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x0(m), zero(m), one(m);
    x0 = m.mk_polynomial(m.mk_var());
    zero = m.mk_zero();
    one  = m.mk_const(rational(1));
    tst_rem((x0^2) + x0, x0, zero);
    tst_rem((x0^2) + x0 + 1, x0, one);
    tst_rem((x0^2) + 2*x0 + 1, 2*x0 + 2, zero);
}

static void tst_lower_bound(polynomial_ref const & p) {
    ENSURE(is_univariate(p));
    std::cout << "---------------\n";
    std::cout << "p: " << p << std::endl;
    reslimit rl; upolynomial::manager um(rl, p.m().m());
    upolynomial::scoped_numeral_vector _p(um);
    um.to_numeral_vector(p, _p);
    std::cout << "_p: "; um.display(std::cout, _p); std::cout << "\n";
    unsigned k = um.nonzero_root_lower_bound(_p.size(), _p.c_ptr());
    std::cout << "_p: "; um.display(std::cout, _p); std::cout << "\n";
    std::cout << "k:  " << k << "\n";
}

static void tst_lower_bound() {
    reslimit rl;
    polynomial::numeral_manager nm;
    polynomial::manager m(rl, nm);
    polynomial_ref x(m), zero(m), one(m);
    x = m.mk_polynomial(m.mk_var());
    zero = m.mk_zero();
    one  = m.mk_const(rational(1));
    tst_lower_bound((x^2) - 2);
    tst_lower_bound((x^5));
    tst_lower_bound((x - 1)*(2*x - 1)*(4*x - 1)*(8*x - 1));
    tst_lower_bound((x - 1)*(2*x - 1)*(4*x - 1)*(8*x - 1)*(16*x - 1));
    tst_lower_bound((x - 1)*(2*x - 1)*(4*x - 1)*(8*x - 1)*(16*x - 1)*(x^3));
    tst_lower_bound((x^5) - x - 1);
    tst_lower_bound((1000*x - 1)*(x - 1));
    tst_lower_bound((x + 1)*(2*x - 1)*(4*x + 1)*(8*x - 1)*(16*x + 1));
    tst_lower_bound((x + 1)*(2*x + 1)*(4*x + 1)*(8*x + 1)*(16*x + 1));
    tst_lower_bound((x^10) - 10*(x^8) + 38*(x^6) - 2*(x^5) - 100*(x^4) - 40*(x^3) + 121*(x^2) - 38*x - 17);
    tst_lower_bound(((x^17) + 5*(x^16) + 3*(x^15) + 10*(x^13) + 13*(x^10) + (x^9) + 8*(x^5) + 3*(x^2) + 7)*(((x^5) - x - 1)^2)*(((x^3) - 2)^2));
    tst_lower_bound((((x^5) - 1000000000)^3)*((3*x - 10000000)^2)*((10*x - 632)^2));
}

void tst_upolynomial() {
    set_verbosity_level(1000);
    enable_trace("mpz_gcd");
    enable_trace("normalize_bug");
    enable_trace("factor_bug");
    enable_trace("factor");
    // enable_trace("mpzp_inv_bug");
    // enable_trace("mpz");
    tst_gcd();
    tst_lower_bound();
    tst_fact();
    tst_rem();
    tst_exact_div();
    tst_isolate_roots5();
    // tst_gcd2();
    // tst_isolate_roots4();
    // tst_isolate_roots3();
    // tst_isolate_roots2();
    // return;
    tst_isolate_roots();
    tst_sturm2();
    tst_convert_q2bq();
    enable_trace("div_bug");
    enable_trace("mpbq_bug");
    tst_translate_q();
    tst_refine();
    tst_refinable();
    tst_sturm();
    tst_remove_one_half();
    tst_isolate_roots();
    tst1();
    tst_zp();
    tst_zp2();
    tst_ext_gcd();
    tst_ext_gcd_z7();
}
