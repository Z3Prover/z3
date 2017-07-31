/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    rcf.cpp

Abstract:

    Testing RCF module

Author:

    Leonardo (leonardo) 2013-01-04

Notes:

--*/
#include "math/realclosure/realclosure.h"
#include "math/realclosure/mpz_matrix.h"
#include "util/rlimit.h"

static void tst1() {
    unsynch_mpq_manager qm;
    reslimit rl;
    rcmanager m(rl, qm);
    scoped_rcnumeral a(m);
#if 0
    a = 10;
    std::cout << sym_pp(a) << std::endl;
    std::cout << sym_pp(eps) << std::endl;
    std::cout << interval_pp(a) << std::endl;
    std::cout << interval_pp(eps) << std::endl;
#endif

    scoped_rcnumeral eps(m);
    m.mk_infinitesimal(eps);
    mpq aux;
    qm.set(aux, 1, 3);
    m.set(a, aux);

#if 0
    std::cout << interval_pp(a) << std::endl;
    std::cout << decimal_pp(eps, 4) << std::endl;
    std::cout << decimal_pp(a) << std::endl;
    std::cout << a + eps << std::endl;
    std::cout << a * eps << std::endl;
    std::cout << (a + eps)*eps - eps << std::endl;
#endif
    std::cout << interval_pp(a - eps*2) << std::endl;
    std::cout << interval_pp(eps + 1) << std::endl;
    scoped_rcnumeral t(m);
    t = (a - eps*2) / (eps + 1);
    std::cout << t << std::endl;
    std::cout << t * (eps + 1) << std::endl;
    a = 10;
    std::cout << (a + eps > a) << std::endl;
    scoped_rcnumeral pi(m);
    m.mk_pi(pi);
    std::cout << pi + 1 << std::endl;
    std::cout << decimal_pp(pi) << std::endl;
    std::cout << decimal_pp(pi + 1) << std::endl;
    scoped_rcnumeral e(m);
    m.mk_e(e);
    t = e + (pi + 1)*2;
    std::cout << t << std::endl;
    std::cout << decimal_pp(t, 10) << std::endl;
    std::cout << (eps + 1 > 1) << std::endl;
    std::cout << interval_pp((a + eps)/(a - eps)) << std::endl;
}

static void tst2() {
    enable_trace("mpz_matrix");
    unsynch_mpq_manager nm;
    small_object_allocator allocator;
    mpz_matrix_manager mm(nm, allocator);
    scoped_mpz_matrix A(mm);
    mm.mk(3, 3, A);
    // Matrix
    // 1 1  1
    // 0 1 -1
    // 0 1  1
    A.set(0, 0, 1); A.set(0, 1, 1); A.set(0, 2,  1);
    A.set(1, 0, 0); A.set(1, 1, 1); A.set(1, 2, -1);
    A.set(2, 0, 0); A.set(2, 1, 1); A.set(2, 2,  1);
    std::cout << A;
    {
        int b[3];
        int c[3] = { 10, -2, 8 };
        std::cout << "solve: " << mm.solve(A, b, c) << "\n";
        for (unsigned i = 0; i < 3; i++) std::cout << b[i] << " ";
        std::cout << "\n";
    }
    scoped_mpz_matrix A2(mm);
    mm.tensor_product(A, A, A2);
    std::cout << A2;
    scoped_mpz_matrix B(mm);
    unsigned cols[] = { 1, 3, 7, 8 };
    mm.filter_cols(A2, 4, cols, B);
    std::cout << B;
    scoped_mpz_matrix C(mm);
    unsigned perm[] = { 8, 7, 6, 5, 4, 3, 2, 1, 0 };
    mm.permute_rows(B, perm, C);
    std::cout << C;
}

static void tst_solve(unsigned n, int _A[], int _b[], int _c[], bool solved) {
    unsynch_mpq_manager nm;
    small_object_allocator allocator;
    mpz_matrix_manager mm(nm, allocator);
    scoped_mpz_matrix A(mm);
    mm.mk(n, n, A);
    for (unsigned i = 0; i < n; i++)
        for (unsigned j = 0; j < n; j++)
            A.set(i, j, _A[i*n + j]);
    svector<int> b;
    b.resize(n, 0);
    if (mm.solve(A, b.c_ptr(), _c)) {
        ENSURE(solved);
        for (unsigned i = 0; i < n; i++) {
            ENSURE(b[i] == _b[i]);
        }
    }
    else {
        ENSURE(!solved);
    }
}

static void tst_lin_indep(unsigned m, unsigned n, int _A[], unsigned ex_sz, unsigned ex_r[]) {
    unsynch_mpq_manager nm;
    small_object_allocator allocator;
    mpz_matrix_manager mm(nm, allocator);
    scoped_mpz_matrix A(mm);
    mm.mk(m, n, A);
    for (unsigned i = 0; i < m; i++)
        for (unsigned j = 0; j < n; j++)
            A.set(i, j, _A[i*n + j]);
    unsigned_vector r;
    r.resize(A.n());
    scoped_mpz_matrix B(mm);
    mm.linear_independent_rows(A, r.c_ptr(), B);
    for (unsigned i = 0; i < ex_sz; i++) {
        ENSURE(r[i] == ex_r[i]);
    }
}

static void tst_denominators() {
    reslimit rl;
    unsynch_mpq_manager qm;
    rcmanager m(rl, qm);
    scoped_rcnumeral a(m);
    scoped_rcnumeral t(m);
    scoped_rcnumeral eps(m);
    m.mk_pi(a);
    m.inv(a);
    m.mk_infinitesimal(eps);
    t = (a - eps*2) / (a*eps + 1);
    // t = t + a * 2;
    scoped_rcnumeral n(m), d(m);
    std::cout << t << "\n";
    m.clean_denominators(t, n, d);
    std::cout << "---->\n" << n << "\n" << d << "\n";
}

void tst_rcf() {
    enable_trace("rcf_clean");
    enable_trace("rcf_clean_bug");
    tst_denominators();
    tst1();
    tst2();
    { int A[] = {0, 1, 1, 1, 0, 1, 1, 1, -1}; int c[] = {10, 4, -4}; int b[] = {-2, 4, 6}; tst_solve(3, A, b, c, true); }
    { int A[] = {1, 1, 1, 0, 1, 1, 0, 1, 1}; int c[] = {3, 2, 2}; int b[] = {1, 1, 1}; tst_solve(3, A, b, c, false); }
    { int A[] = {1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, -1}; unsigned r[] = {0, 1, 4}; tst_lin_indep(5, 3, A, 3, r); }
    { int A[] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, -1}; unsigned r[] = {0, 4}; tst_lin_indep(5, 3, A, 2, r); }
    { int A[] = {1, 1, 1, 1, 1, 1, 1, 0, 1, 2, 1, 2, 3, 1, 3}; unsigned r[] = {0, 2}; tst_lin_indep(5, 3, A, 2, r); }
}
