/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    polynomial_factorization.cpp

Abstract:

    Testing of factorization.

Author:

    Dejan (t-dejanj) 2011-11-29

Notes:

--*/
#include"upolynomial_factorization_int.h"
#include"timeit.h"
#include"polynomial.h"
#include"rlimit.h"
#if 0
#include"polynomial_factorization.h"
#endif

using std::cout;
using std::endl;

// some prime numbers
unsigned primes[] = {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29
};

// [i,l]: how many factors the Knuth example has over p_i, when i = 0 it's Z, p_1 = 2, for l=0 distinct, for l = 1 total
unsigned knuth_factors[2][11] = {
    // x^8 + x^6 + 10*x^4 + 10*x^3 + 8*x^2 + 2*x + 8
    {2, 2, 3, 3, 2, 3, 1, 4, 3, 1, 1},
    {8, 2, 3, 3, 2, 3, 1, 4, 3, 1, 1},
};

// [k,l,i]: how many factors the S_k has over p_i, when i = 0 it's Z, p_1 = 2, for l=0 distinct, for l = 1 total
unsigned swinnerton_dyer_factors[5][2][11] = {
    // S1 = (x^2) - 2
    {
    //   2, 3, 5, 7,11,13,17,19,23,29, Z
        {1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1},
        {2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1}
    },
    // S2 = (x^4) - 10*(x^2) + 1
    {
        {1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1},
        {4, 2, 2, 2, 2, 2, 2, 2, 4, 2, 1}
    },
    // S3 = (x^8) - 40*(x^6) + 352*(x^4) - 960*(x^2) + 576
    {
        {1, 2, 2, 4, 4, 4, 4, 4, 4, 4, 1},
        {8, 6, 4, 4, 4, 4, 4, 4, 4, 4, 1}
    },
    // S4 = (x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225
    {
        {1, 4, 3, 4, 8, 8, 8, 8, 8, 8, 1},
        {16, 12, 10, 8, 8, 8, 8, 8, 8, 8, 1}
    },
    // SA = S1*S2*S3*S4
    {
    //p = 2,  3,  5,  7, 11, 13, 17, 19, 23, 29, Z
        { 2,  6,  3,  6, 15, 11, 16, 15, 18, 15, 1},
        {30, 21, 17, 16, 15, 15, 16, 15, 18, 15, 1}
    }
};

int random_polynomial[20][2][11] = {
    {
        // 3*x^10 + 2*x^9 + 4*x^8 + 4*x^7 + 4*x^6 + x^5 + 3*x^2 + 3*x
        { 4, 3, 4, 4, 3, 4, 4, 4, 3, 4, 2 },
        { 7, 7, 4, 4, 3, 4, 4, 4, 3, 4, 2 },
    },
    {
        // 4*x^9 + 4*x^8 + x^7 + x^6 + 2*x^5 + 3*x^4 + 4*x^2 + 4*x
        { 2, 2, 3, 3, 4, 2, 5, 3, 4, 2, 2 },
        { 5, 2, 3, 3, 4, 2, 5, 3, 5, 2, 2 },
    },
    {
        // 3*x^10 + 4*x^9 + 3*x^8 + x^6 + 4*x^5 + 4*x^4 + x^2
        { 3, 2, 4, 4, 5, 3, 4, 2, 4, 5, 2 },
        { 6, 3, 5, 5, 6, 4, 5, 3, 5, 7, 3 },
    },
    {
        // x^10 + 4*x^9 + x^8 + 3*x^7 + 3*x^4 + 3*x^3 + x^2 + 4*x
        { 3, 4, 4, 3, 3, 3, 4, 4, 5, 3, 2 },
        { 8, 4, 4, 3, 3, 3, 4, 4, 5, 3, 2 },
    },
    {
        // x^9 + 2*x^8 + 3*x^7 + x^6 + 2*x^5 + 4*x^4 + 3*x^2
        { 3, 3, 3, 3, 4, 4, 4, 3, 3, 4, 2 },
        { 5, 6, 4, 5, 5, 6, 5, 4, 4, 5, 3 },
    },
    {
        // x^10 + x^9 + 4*x^7 + x^6 + 3*x^5 + x^4 + x^3 + x
        { 3, 2, 3, 3, 3, 5, 3, 2, 4, 4, 2 },
        { 3, 2, 3, 3, 3, 5, 3, 2, 4, 4, 2 },
    },
    {
        // 4*x^10 + 4*x^9 + x^8 + 2*x^7 + 3*x^6 + 4*x^5 + 3*x^4 + x^3 + 2*x^2 + 4*x
        { 3, 3, 2, 5, 3, 4, 2, 4, 5, 5, 2 },
        { 5, 3, 2, 5, 3, 4, 2, 4, 5, 5, 2 },
    },
    {
        // 3*x^10 + 4*x^9 + 3*x^8 + x^7 + x^6 + 2*x^5 + x^4 + 2*x^3 + 2*x^2 + x
        { 3, 4, 6, 4, 4, 4, 4, 6, 6, 4, 3 },
        { 4, 4, 7, 4, 4, 4, 4, 6, 6, 4, 3 },
    },
    {
        // 4*x^10 + x^9 + x^7 + 2*x^5 + 3*x^3 + x^2 + 4*x
        { 3, 3, 3, 4, 4, 5, 4, 5, 2, 4, 2 },
        { 4, 4, 3, 4, 4, 5, 4, 5, 2, 4, 2 },
    },
    {
        // x^10 + 3*x^9 + 3*x^8 + x^7 + 3*x^6 + 3*x^5 + 3*x^4 + x^2 + 3*x
        { 2, 3, 4, 4, 3, 3, 4, 3, 3, 4, 2 },
        { 2, 4, 5, 4, 3, 3, 4, 3, 3, 4, 2 },
    },
    {
        // x^10 + x^9 + 2*x^8 + x^7 + 4*x^6 + 2*x^5 + 3*x^4 + 4*x^3 + x^2 + 2*x
        { 3, 4, 4, 3, 3, 3, 3, 4, 5, 3, 2 },
        { 4, 4, 4, 3, 3, 3, 3, 4, 5, 3, 2 },
    },
    {
        // 3*x^9 + x^8 + 3*x^7 + 3*x^6 + x^5 + 2*x^4 + 4*x^3 + 4*x^2 + 3*x
        { 4, 3, 3, 3, 5, 3, 6, 4, 2, 2, 2 },
        { 6, 4, 3, 3, 5, 3, 6, 4, 2, 2, 2 },
    },
    {
        // 2*x^10 + 3*x^9 + 2*x^8 + 4*x^7 + x^6 + 3*x^5 + 2*x^3 + 3*x^2 + 2*x + 2
        { 3, 3, 3, 5, 4, 5, 6, 7, 4, 6, 3 },
        { 8, 4, 3, 7, 4, 5, 6, 7, 4, 7, 3 },
    },
    {
        // 3*x^10 + x^9 + 4*x^8 + 2*x^7 + x^6 + 4*x^5 + x^4 + 3*x^3 + x + 2
        { 3, 3, 3, 2, 6, 4, 4, 4, 3, 3, 2 },
        { 3, 3, 3, 2, 6, 5, 4, 5, 3, 3, 2 },
    },
    {
        // 4*x^10 + 2*x^9 + x^8 + x^6 + x^5 + 3*x^4 + 4*x^3 + x^2 + x
        { 3, 4, 2, 4, 4, 4, 4, 2, 3, 3, 2 },
        { 6, 4, 2, 4, 4, 4, 4, 2, 3, 3, 2 },
    },
    {
        // 4*x^10 + 2*x^7 + 4*x^6 + 2*x^3 + x
        { 1, 3, 3, 3, 4, 4, 4, 3, 3, 2, 2 },
        { 1, 3, 3, 3, 4, 4, 4, 3, 3, 2, 2 },
    },
    {
        // 4*x^10 + x^9 + x^8 + 4*x^7 + 4*x^4 + 2*x^2 + x + 4
        { 3, 4, 2, 5, 3, 6, 3, 6, 3, 3, 2 },
        { 3, 6, 2, 5, 3, 6, 3, 6, 3, 3, 2 },
    },
    {
        // 3*x^10 + 2*x^8 + x^7 + x^6 + 3*x^4 + 3*x^3 + 4*x^2 + 3*x
        { 4, 3, 4, 3, 3, 3, 2, 4, 4, 3, 2 },
        { 5, 4, 4, 3, 3, 3, 2, 4, 4, 3, 2 },
    },
    {
        // x^10 + 2*x^9 + 2*x^6 + 4*x^3 + 4*x^2
        { 1, 2, 2, 3, 3, 4, 3, 3, 3, 3, 2 },
        { 10, 3, 3, 4, 4, 6, 4, 4, 4, 4, 3 },
    },
    {
        // x^10 + 2*x^9 + 2*x^8 + 4*x^7 + 4*x^6 + x^5 + x^3 + x^2 + 3*x
        { 2, 4, 2, 3, 3, 3, 5, 5, 6, 2, 2 },
        { 2, 5, 2, 3, 3, 3, 5, 5, 6, 2, 2 },
    }
};

#if 0
static void tst_square_free_finite_1() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    // example from Knuth, p. 442
    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    // polynomials \prod_{i < p} (x - i)^i
    for (unsigned prime_i = 0; prime_i < 5; ++ prime_i)
    {
        int p = primes[prime_i];

        // make the polynomial
        polynomial_ref f(pm);
        f = x - 1;
        for (int i = 2; i < p; ++ i) {
            f = f*((x + (-i))^i);
        }
        cout << "Factoring " << f << " into square-free over Z_" << p << endl;

        // convert to univariate over Z_p
        upolynomial::zp_manager upm(nm);
        upm.set_zp(p);
        upolynomial::numeral_vector f_u;
        upm.to_numeral_vector(f, f_u);

        cout << "Input: "; upm.display(cout, f_u); cout << endl;

        // factor it
        upolynomial::zp_factors f_factors(upm);
        cout << "Start: " << f_factors << endl;

        upolynomial::zp_square_free_factor(upm, f_u, f_factors);

        upolynomial::numeral_vector mult;
        f_factors.multiply(mult);
        cout << "Multiplied: "; upm.display(cout, mult); cout << endl;

        SASSERT(upm.eq(mult, f_u));

        // remove the temps
        upm.reset(f_u);
        upm.reset(mult);
    }
}

static void tst_factor_finite_1() {

    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    // example from Knuth, p. 442
    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());
    polynomial_ref K(pm);
    K = (x^8) + (x^6) + 10*(x^4) + 10*(x^3) + 8*(x^2) + 2*x + 8;

    // factor them for all the prime numbers
    for (unsigned prime_i = 0; prime_i < sizeof(primes)/sizeof(unsigned); ++ prime_i)
    {
        // make the Z_p
        unsigned prime = primes[prime_i];
        upolynomial::zp_manager upm(nm);
        upm.set_zp(prime);

        // make the polynomial in Z_p
        upolynomial::numeral_vector K_u;
        upm.to_numeral_vector(K, K_u);

        cout << "Factoring " << K << "("; upm.display(cout, K_u); cout << ") in Z_" << prime << endl;
        cout << "Expecting " << knuth_factors[0][prime_i] << " distinct factors, " << knuth_factors[1][prime_i] << " total" << endl;

        // factor it
        upolynomial::zp_factors factors(upm);
        /* bool factorized = */ upolynomial::zp_factor(upm, K_u, factors);

        // check the result
        unsigned distinct = factors.distinct_factors();
        unsigned total = factors.total_factors();

        cout << "Got " << factors << endl;
        cout << "Thats " << distinct << " distinct factors, " << total << " total" << endl;

        SASSERT(knuth_factors[0][prime_i] == distinct);
        SASSERT(knuth_factors[1][prime_i] == total);

        upolynomial::numeral_vector multiplied;
        factors.multiply(multiplied);
        SASSERT(upm.eq(K_u, multiplied));
        upm.reset(multiplied);

        // remove the temp
        upm.reset(K_u);
    }
}

static void tst_factor_finite_2() {

    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    // Swinnerton-Dyer polynomials (irreducible, modular factors of degree at most 2)
    polynomial_ref S1 = (x^2) - 2;
    polynomial_ref S2 = (x^4) - 10*(x^2) + 1;
    polynomial_ref S3 = (x^8) - 40*(x^6) + 352*(x^4) - 960*(x^2) + 576;
    polynomial_ref S4 = (x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225;

    vector<polynomial_ref> S;
    S.push_back(S1);
    S.push_back(S2);
    S.push_back(S3);
    S.push_back(S4);
    S.push_back(S1*S2*S3*S4);

    // factor all the S_i them for all the prime numbers
    for (unsigned S_i = 0; S_i < S.size(); ++ S_i) {
        for (unsigned prime_i = 0; prime_i < sizeof(primes)/sizeof(unsigned); ++ prime_i) {
            unsigned prime = primes[prime_i];

            upolynomial::zp_manager upm(nm);
            upm.set_zp(prime);

            upolynomial::numeral_vector S_i_u;
            upm.to_numeral_vector(S[S_i], S_i_u);

            cout << "Factoring "; upm.display(cout, S_i_u); cout << " over Z_" << prime << endl;
            cout << "Expecting " << swinnerton_dyer_factors[S_i][0][prime_i] << " distinct factors, " << swinnerton_dyer_factors[S_i][1][prime_i] << " total" << endl;

            upolynomial::zp_factors factors(upm);
            upolynomial::zp_factor(upm, S_i_u, factors);

            // check the result
            unsigned distinct = factors.distinct_factors();
            unsigned total = factors.total_factors();

            cout << "Got " << factors << endl;
            cout << "Thats " << distinct << " distinct factors, " << total << " total" << endl;

            SASSERT(swinnerton_dyer_factors[S_i][0][prime_i] == distinct);
            SASSERT(swinnerton_dyer_factors[S_i][1][prime_i] == total);

            upolynomial::numeral_vector multiplied;
            factors.multiply(multiplied);
            SASSERT(upm.eq(S_i_u, multiplied));
            upm.reset(multiplied);

            // remove the temp
            upm.reset(S_i_u);
        }
    }
}

static void tst_factor_finite_3() {

    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    // random polynomials
    vector<polynomial_ref> random_p;
    random_p.push_back( 3*(x^10) + 2*(x^9) + 4*(x^8) + 4*(x^7) + 4*(x^6) + 1*(x^5) + 3*(x^2) + 3*x + 0 );
    random_p.push_back( 4*(x^9) + 4*(x^8) + 1*(x^7) + 1*(x^6) + 2*(x^5) + 3*(x^4) + 4*(x^2) + 4*x + 0 );
    random_p.push_back( 3*(x^10) + 4*(x^9) + 3*(x^8) + 1*(x^6) + 4*(x^5) + 4*(x^4) + 1*(x^2) + 0 );
    random_p.push_back( 1*(x^10) + 4*(x^9) + 1*(x^8) + 3*(x^7) + 3*(x^4) + 3*(x^3) + 1*(x^2) + 4*x + 0 );
    random_p.push_back( 1*(x^9) + 2*(x^8) + 3*(x^7) + 1*(x^6) + 2*(x^5) + 4*(x^4) + 3*(x^2) + 0 );
    random_p.push_back( 1*(x^10) + 1*(x^9) + 4*(x^7) + 1*(x^6) + 3*(x^5) + 1*(x^4) + 1*(x^3) + 1*x + 0 );
    random_p.push_back( 4*(x^10) + 4*(x^9) + 1*(x^8) + 2*(x^7) + 3*(x^6) + 4*(x^5) + 3*(x^4) + 1*(x^3) + 2*(x^2) + 4*x + 0 );
    random_p.push_back( 3*(x^10) + 4*(x^9) + 3*(x^8) + 1*(x^7) + 1*(x^6) + 2*(x^5) + 1*(x^4) + 2*(x^3) + 2*(x^2) + 1*x + 0 );
    random_p.push_back( 4*(x^10) + 1*(x^9) + 1*(x^7) + 2*(x^5) + 3*(x^3) + 1*(x^2) + 4*x + 0 );
    random_p.push_back( 1*(x^10) + 3*(x^9) + 3*(x^8) + 1*(x^7) + 3*(x^6) + 3*(x^5) + 3*(x^4) + 1*(x^2) + 3*x + 0 );
    random_p.push_back( 1*(x^10) + 1*(x^9) + 2*(x^8) + 1*(x^7) + 4*(x^6) + 2*(x^5) + 3*(x^4) + 4*(x^3) + 1*(x^2) + 2*x + 0 );
    random_p.push_back( 3*(x^9) + 1*(x^8) + 3*(x^7) + 3*(x^6) + 1*(x^5) + 2*(x^4) + 4*(x^3) + 4*(x^2) + 3*x + 0 );
    random_p.push_back( 2*(x^10) + 3*(x^9) + 2*(x^8) + 4*(x^7) + 1*(x^6) + 3*(x^5) + 2*(x^3) + 3*(x^2) + 2*x + 2 );
    random_p.push_back( 3*(x^10) + 1*(x^9) + 4*(x^8) + 2*(x^7) + 1*(x^6) + 4*(x^5) + 1*(x^4) + 3*(x^3) + 1*x + 2 );
    random_p.push_back( 4*(x^10) + 2*(x^9) + 1*(x^8) + 1*(x^6) + 1*(x^5) + 3*(x^4) + 4*(x^3) + 1*(x^2) + 1*x + 0 );
    random_p.push_back( 4*(x^10) + 2*(x^7) + 4*(x^6) + 2*(x^3) + 1*x + 0 );
    random_p.push_back( 4*(x^10) + 1*(x^9) + 1*(x^8) + 4*(x^7) + 4*(x^4) + 2*(x^2) + 1*x + 4 );
    random_p.push_back( 3*(x^10) + 2*(x^8) + 1*(x^7) + 1*(x^6) + 3*(x^4) + 3*(x^3) + 4*(x^2) + 3*x + 0 );
    random_p.push_back( 1*(x^10) + 2*(x^9) + 2*(x^6) + 4*(x^3) + 4*(x^2) + 0 );
    random_p.push_back( 1*(x^10) + 2*(x^9) + 2*(x^8) + 4*(x^7) + 4*(x^6) + 1*(x^5) + 1*(x^3) + 1*(x^2) + 3*x + 0 );

    // factor all the randoms them for all the prime numbers
    for (unsigned random_i = 0; random_i < random_p.size(); ++ random_i) {
        for (unsigned prime_i = 0; prime_i < sizeof(primes)/sizeof(unsigned); ++ prime_i) {
            unsigned prime = primes[prime_i];

            upolynomial::zp_manager upm(nm);
            upm.set_zp(prime);

            upolynomial::numeral_vector poly;
            upm.to_numeral_vector(random_p[random_i], poly);

            cout << "Factoring "; upm.display(cout, poly); cout << " over Z_" << prime << endl;
            cout << "Expecting " << swinnerton_dyer_factors[random_i][0][prime_i] << " distinct factors, " << random_polynomial[random_i][1][prime_i] << " total" << endl;

            upolynomial::zp_factors factors(upm);
            upolynomial::zp_factor(upm, poly, factors);

            // check the result
            unsigned distinct = factors.distinct_factors();
            unsigned total = factors.total_factors();

            cout << "Got " << factors << endl;
            cout << "Thats " << distinct << " distinct factors, " << total << " total" << endl;

            // SASSERT(random_polynomial[random_i][0][prime_i] == distinct);
            // SASSERT(random_polynomial[random_i][1][prime_i] == total);

            upolynomial::numeral_vector multiplied;
            factors.multiply(multiplied);
            bool equal = upm.eq(poly, multiplied);
            cout << (equal ? "equal" : "not equal") << endl;
            SASSERT(equal);
            upm.reset(multiplied);

            // remove the temp
            upm.reset(poly);
        }
    }
}

static void tst_factor_enumeration() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    vector<polynomial_ref> factors;
    for (int i = 0; i < 5; ++ i) {
        polynomial_ref factor(pm);
        factor = x + i;
        factors.push_back(factor);
    }

    upolynomial::manager upm(nm);

    upolynomial::zp_manager upm_13(nm);
    upm_13.set_zp(13);
    upolynomial::zp_factors factors_13(upm_13);

    upolynomial::numeral constant;
    nm.set(constant, 10);
    factors_13.set_constant(constant);

    for (unsigned i = 0; i < 5; ++ i) {
        upolynomial::numeral_vector ufactor;
        upm_13.to_numeral_vector(factors[i], ufactor);
        factors_13.push_back(ufactor, 1);
        upm.reset(ufactor);
    }

    cout << "All: " << factors_13 << endl;

    upolynomial::factorization_degree_set degrees(factors_13);
    degrees.display(cout); cout << endl;

    scoped_mpz_vector left(nm), right(nm);
    upolynomial::ufactorization_combination_iterator it(factors_13, degrees);
    unsigned i = 0;
    it.display(cout);
    bool remove = false;
    while (it.next(remove)) {
        it.left(left);
        it.right(right);
        cout << "Left " << i  << ": "; upm.display(cout, left); cout << endl;
        cout << "Right " << i << ": "; upm.display(cout, right); cout << endl;
        i ++;
        if (i % 3 == 0) {
            remove = true;
        } else {
            remove = false;
        }
        it.display(cout);
    }
    // SASSERT(i == 15);

    return;

    for (unsigned i = 0; i < 5; ++ i) {
        factors_13.set_degree(i, factors_13.get_degree(i) + i);
    }
    cout << "Different: " << factors_13 << " of degree " << factors_13.get_degree() << endl;
    upolynomial::factorization_degree_set degrees1(factors_13);
    degrees1.display(cout); cout << endl; // [0, ..., 15]

    polynomial_ref tmp1 = (x^3) + 1;
    polynomial_ref tmp2 = (x^5) + 2;
    polynomial_ref tmp3 = (x^7) + 3;
    upolynomial::numeral_vector up1, up2, up3;
    upm_13.to_numeral_vector(tmp1, up1);
    upm_13.to_numeral_vector(tmp2, up2);
    upm_13.to_numeral_vector(tmp3, up3);
    upolynomial::zp_factors tmp(upm_13);
    tmp.push_back(up1, 1);
    tmp.push_back(up2, 1);
    tmp.push_back(up3, 1);
    upm_13.reset(up1);
    upm_13.reset(up2);
    upm_13.reset(up3);

    cout << "Different: " << tmp << " of degree " << tmp.get_degree() << endl;
    upolynomial::factorization_degree_set degrees2(tmp);
    degrees2.display(cout); cout << endl;

    tmp1 = (x^2) + 1;
    tmp2 = (x^10) + 2;
    tmp3 = x + 3;
    upm_13.to_numeral_vector(tmp1, up1);
    upm_13.to_numeral_vector(tmp2, up2);
    upm_13.to_numeral_vector(tmp3, up3);
    tmp.clear();
    tmp.push_back(up1, 2);
    tmp.push_back(up2, 1);
    tmp.push_back(up3, 1);
    cout << "Different: " << tmp << " of degree " << tmp.get_degree() << endl;
    upm_13.reset(up1);
    upm_13.reset(up2);
    upm_13.reset(up3);
    upolynomial::factorization_degree_set degrees3(tmp);
    degrees3.display(cout); cout << endl;
    degrees1.intersect(degrees3);
    degrees1.display(cout); cout << endl;
}

static void tst_factor_square_free_univariate_1(unsigned max_length) {

    polynomial::numeral_manager nm;
    upolynomial::numeral test;
    upolynomial::numeral p;
    nm.set(test, -9);
    nm.set(p, 5);
    nm.mod(test, p, test);

    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    cout << "R.<x> = QQ['x']" << endl;

    // let's start with \prod (p_i x^{p_{i+1} - p_{i+1})
    unsigned n_primes = sizeof(primes)/sizeof(unsigned);
    max_length = std::min(max_length, n_primes);
    for(unsigned length = 1; length < max_length; ++ length) {

        // starting from prime_i going for length
        for(unsigned start_i = 0; start_i < n_primes; ++ start_i) {

            polynomial_ref f(pm);

            bool first = true;
            for (unsigned prime_i = 0; prime_i < length; ++ prime_i) {
                int p1 = primes[(start_i + prime_i) % n_primes];
                int p2 = primes[(start_i + prime_i + 1) % n_primes];
                if (first) {
                    f = (p1*(x^p2) - p2);
                    first = false;
                } else {
                    f = f*(p1*(x^p2) - p2);
                }
            }

            upolynomial::manager upm(nm);
            scoped_mpz_vector f_u(nm);
            upm.to_numeral_vector(f, f_u);

            cout << "factoring "; upm.display(cout, f_u); cout << endl;
            cout << "expecting " << length << " factors ";
            upolynomial::factors factors(upm);
            /* bool ok = */ upolynomial::factor_square_free(upm, f_u, factors);
            cout << "got " << factors << endl;

            SASSERT(factors.distinct_factors() == length);
        }
    }
}

static void tst_factor_square_free_univariate_2() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    // Swinnerton-Dyer polynomials (irreducible, modular factors of degree at most 2)
    polynomial_ref S1 = (x^2) - 2;
    polynomial_ref S2 = (x^4) - 10*(x^2) + 1;
    polynomial_ref S3 = (x^8) - 40*(x^6) + 352*(x^4) - 960*(x^2) + 576;
    polynomial_ref S4 = (x^16) - 136*(x^14) + 6476*(x^12) - 141912*(x^10) + 1513334*(x^8) - 7453176*(x^6) + 13950764*(x^4) - 5596840*(x^2) + 46225;

    vector<polynomial_ref> S;
    S.push_back(S1);
    S.push_back(S2);
    S.push_back(S3);
    S.push_back(S4);

    upolynomial::manager upm(nm);

    // factor all the S_i them for all the prime numbers
    for (unsigned S_i = 0; S_i < S.size(); ++ S_i) {
        upolynomial::numeral_vector S_i_u;
        upm.to_numeral_vector(S[S_i], S_i_u);

        cout << "Factoring "; upm.display(cout, S_i_u); cout << " over Z " << endl;
        upolynomial::factors factors(upm);
        upolynomial::factor_square_free(upm, S_i_u, factors);

        // check the result
        cout << "Got " << factors << endl;

        // remove the temp
        upm.reset(S_i_u);
    }
}

static void tst_factor_square_free_univariate_3() {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    polynomial_ref deg70 = (x^70) - 6*(x^65) - (x^60) + 60*(x^55) - 54*(x^50) - 230*(x^45) + 274*(x^40) + 542*(x^35) - 615*(x^30)  - 1120*(x^25) + 1500*(x^20) - 160*(x^15) - 395*(x^10) + 76*(x^5) + 34;

    upolynomial::manager upm(nm);
    upolynomial::numeral_vector deg70_u;

    upm.to_numeral_vector(deg70, deg70_u);

    cout << "Factoring "; upm.display(cout, deg70_u); cout << " over Z " << endl;
    upolynomial::factors factors(upm);
    upolynomial::factor_square_free(upm, deg70_u, factors);

    cout << "Got " << factors << endl;

    upm.reset(deg70_u);
}
#endif

void tst_factor_swinnerton_dyer_big(unsigned max) {
    polynomial::numeral_manager nm;
    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

    vector<polynomial_ref> roots;
    vector<polynomial::var> vars;

    unsigned n = std::min(max, static_cast<unsigned>(sizeof(primes)/sizeof(unsigned)));
    for(unsigned prime_i = 0; prime_i < n; ++ prime_i) {

        int prime = primes[prime_i];

        cout << "Computing Swinnerton-Dyer[" << prime_i + 1 << "]" << endl;

        polynomial_ref y(pm);
        vars.push_back(pm.mk_var());
        y = pm.mk_polynomial(vars.back());

        polynomial_ref p(pm);
        p = (y^2) - prime;
        roots.push_back(p);

        polynomial_ref computation = x;
        for (unsigned i = 0; i < roots.size(); ++ i) {
            polynomial_ref var(pm);
            var = pm.mk_polynomial(vars[i]);
            computation = computation - var;
        }

        {
            timeit timer(true, "computing swinnerton-dyer");

            for (unsigned i = 0; i < roots.size(); ++ i) {
                polynomial_ref tmp(pm);
                pm.resultant(computation, roots[i], vars[i], tmp);
                computation = tmp;
            }
        }

        cout << "Computed Swinnerton-Dyer[" << prime_i + 1 << "], degree = " << pm.total_degree(computation) << ", size = " << pm.size(computation) << endl;

        cout << "Starting factoring " << endl;

        {
            timeit timer(true, "factoring swinnerton-dyer");

            reslimit rl;
            upolynomial::manager upm(rl, nm);
            scoped_mpz_vector sd_u(nm);
            upm.to_numeral_vector(computation, sd_u);
            upolynomial::factors factors(upm);
            upolynomial::factor_square_free(upm, sd_u, factors);
            cout << "Got " << factors.distinct_factors() << " factors" << endl;
        }

    }
}

static void tst_factor_square_free_multivariate_1(unsigned max_n) {
#if 0
    polynomial::numeral_manager nm;
    upolynomial::numeral test;
    upolynomial::numeral p;
    nm.set(test, -9);
    nm.set(p, 5);
    nm.mod(test, p, test);

    reslimit rl; polynomial::manager pm(rl, nm);

    polynomial_ref x(pm);
    x = pm.mk_polynomial(pm.mk_var());

	polynomial_ref y(pm);
    y = pm.mk_polynomial(pm.mk_var());

    // lets start simple x^n - y^n
    for (unsigned prime_i = 0; prime_i < sizeof(primes)/sizeof(unsigned); ++ prime_i) {
		unsigned prime = primes[prime_i];

		if (prime > max_n) {
			break;
		}

		polynomial_ref f = (x^prime) - (y^prime);
		cout << "factoring: " << f << endl;

		// factor
		polynomial::factors factors(pm);
		polynomial::factor_square_free_primitive(f, factors);

		cout << "got: " << factors << endl;
	}
#endif
}


void tst_polynomial_factorization() {

    enable_trace("polynomial::factorization");
    // enable_trace("polynomial::factorization::bughunt");
	enable_trace("polynomial::factorization::multivariate");
    // enable_trace("upolynomial");

    // Z_p square-free factorization tests
    // tst_square_free_finite_1();

    // Z_p factorization tests
    // tst_factor_finite_1();
    // tst_factor_finite_2();
    // tst_factor_finite_3();

    // Z factorization
    // tst_factor_enumeration();
    // tst_factor_square_free_univariate_1(3);
    // tst_factor_square_free_univariate_2();
    // tst_factor_square_free_univariate_3();
    // tst_factor_swinnerton_dyer_big(3);

    // Multivariate factorization
    tst_factor_square_free_multivariate_1(3);
}
