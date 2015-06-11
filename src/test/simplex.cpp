
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "sparse_matrix.h"
#include "sparse_matrix_def.h"
#include "simplex.h"
#include "simplex_def.h"
#include "mpq_inf.h"
#include "vector.h"
#include "rational.h"

#define R rational
typedef simplex::simplex<simplex::mpz_ext> Simplex;
typedef simplex::sparse_matrix<simplex::mpz_ext> sparse_matrix;

static vector<R> vec(int i, int j) {
    vector<R> nv;
    nv.resize(2);
    nv[0] = R(i);
    nv[1] = R(j);
    return nv;
}

static vector<R> vec(int i, int j, int k) {
    vector<R> nv = vec(i, j);
    nv.push_back(R(k));
    return nv;
}

static vector<R> vec(int i, int j, int k, int l) {
    vector<R> nv = vec(i, j, k);
    nv.push_back(R(l));
    return nv;
}

static vector<R> vec(int i, int j, int k, int l, int x) {
    vector<R> nv = vec(i, j, k, l);
    nv.push_back(R(x));
    return nv;
}

static vector<R> vec(int i, int j, int k, int l, int x, int y) {
    vector<R> nv = vec(i, j, k, l, x);
    nv.push_back(R(y));
    return nv;
}

static vector<R> vec(int i, int j, int k, int l, int x, int y, int z) {
    vector<R> nv = vec(i, j, k, l, x, y);
    nv.push_back(R(z));
    return nv;
}



void add_row(Simplex& S, vector<R> const& _v, R const& _b, bool is_eq = false) {
    unsynch_mpz_manager m;
    unsigned_vector vars;
    vector<R> v(_v);
    R b(_b);
    R l(denominator(b));
    scoped_mpz_vector coeffs(m);
    for (unsigned i = 0; i < v.size(); ++i) {
        l = lcm(l, denominator(v[i]));
        vars.push_back(i);
        S.ensure_var(i);
    }
    b *= l;
    b.neg();
    for (unsigned i = 0; i < v.size(); ++i) {
        v[i] *= l;
        coeffs.push_back(v[i].to_mpq().numerator());
    }
    unsigned nv = S.get_num_vars();
    vars.push_back(nv);
    vars.push_back(nv+1);
    S.ensure_var(nv);
    S.ensure_var(nv+1);
    coeffs.push_back(mpz(-1));
    coeffs.push_back(b.to_mpq().numerator());
    mpq_inf one(mpq(1),mpq(0));
    mpq_inf zero(mpq(0),mpq(0));
    SASSERT(vars.size() == coeffs.size());
    S.set_lower(nv, zero);
    if (is_eq) S.set_upper(nv, zero);
    S.set_lower(nv+1, one);
    S.set_upper(nv+1, one);
    S.add_row(nv, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
}

static void feas(Simplex& S) {
    S.display(std::cout);
    lbool is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";
    S.display(std::cout);
}

static void test1() {
    Simplex S;
    add_row(S, vec(1,0), R(1));
    add_row(S, vec(0,1), R(1));
    add_row(S, vec(1,1), R(1));
    feas(S);
}

static void test2() {
    Simplex S;
    add_row(S, vec(1, 0), R(1));
    add_row(S, vec(0, 1), R(1));
    add_row(S, vec(1, 1), R(1), true);
    feas(S);
}

static void test3() {
    Simplex S;
    add_row(S, vec(-1, 0), R(-1));
    add_row(S, vec(0, -1), R(-1));
    add_row(S, vec(1, 1), R(1), true);
    feas(S);
}

static void test4() {
    Simplex S;
    add_row(S, vec(1, 0), R(1));
    add_row(S, vec(0, -1), R(-1));
    add_row(S, vec(1, 1), R(1), true);
    feas(S);
}

void tst_simplex() {
    Simplex S;

    std::cout << "simplex\n";

    lbool is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";

    unsynch_mpz_manager m;
    unsynch_mpq_inf_manager em;
    scoped_mpz_vector coeffs(m);
    svector<unsigned> vars;
    for (unsigned i = 0; i < 5; ++i) {
        S.ensure_var(i);
        vars.push_back(i);
        coeffs.push_back(mpz(i+1));
    }

    Simplex::row r = S.add_row(1, coeffs.size(), vars.c_ptr(), coeffs.c_ptr());
    is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";
    S.display(std::cout);
    _scoped_numeral<unsynch_mpq_inf_manager> num(em); 
    num = std::make_pair(mpq(1), mpq(0));
    S.set_lower(0, num);
    S.set_upper(0, num);

    is_sat = S.make_feasible();
    std::cout << "feasible: " << is_sat << "\n";
    S.display(std::cout);

    test1();
    test2();
    test3();
    test4();
}
