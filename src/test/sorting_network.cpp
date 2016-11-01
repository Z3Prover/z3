
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "trace.h"
#include "vector.h"
#include "ast.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"
#include "sorting_network.h"
#include "smt_kernel.h"
#include "model_smt2_pp.h"
#include "smt_params.h"
#include "ast_util.h"



struct ast_ext {
    ast_manager& m;
    ast_ext(ast_manager& m):m(m) {}
    typedef expr* T;
    typedef expr_ref_vector vector;
    T mk_ite(T a, T b, T c) {
        return m.mk_ite(a, b, c);
    }
    T mk_le(T a, T b) {
        if (m.is_bool(a)) {
                return m.mk_implies(a, b);
        }
        UNREACHABLE();
        return 0;
    }
    T mk_default() {
        return m.mk_false();
    }
};



struct unsigned_ext {
    unsigned_ext() {}
    typedef unsigned T;
    typedef svector<unsigned> vector;
    T mk_ite(T a, T b, T c) {
        return (a==1)?b:c;
    }
    T mk_le(T a, T b) {
        return (a <= b)?1:0;
    }
    T mk_default() {
        return 0;
    }
};


static void is_sorted(svector<unsigned> const& v) {
    for (unsigned i = 0; i + 1 < v.size(); ++i) {
        SASSERT(v[i] <= v[i+1]);
    }
}

static void test_sorting1() {
    svector<unsigned> in, out;
    unsigned_ext uext;
    sorting_network<unsigned_ext> sn(uext);

    in.push_back(0);
    in.push_back(1);
    in.push_back(0);
    in.push_back(1);
    in.push_back(1);
    in.push_back(0);

    sn(in, out);

    is_sorted(out);
    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << out[i];
    }
    std::cout << "\n";
}

static void test_sorting2() {
    svector<unsigned> in, out;
    unsigned_ext uext;
    sorting_network<unsigned_ext> sn(uext);

    in.push_back(0);
    in.push_back(1);
    in.push_back(2);
    in.push_back(1);
    in.push_back(1);
    in.push_back(3);

    sn(in, out);

    is_sorted(out);

    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << out[i];
    }
    std::cout << "\n";
}

static void test_sorting4_r(unsigned i, svector<unsigned>& in) {
    if (i == in.size()) {
        svector<unsigned> out;
        unsigned_ext uext;
        sorting_network<unsigned_ext> sn(uext);
        sn(in, out);
        is_sorted(out);
        std::cout << "sorted\n";
    }
    else {
        in[i] = 0;
        test_sorting4_r(i+1, in);
        in[i] = 1;
        test_sorting4_r(i+1, in);
    }
}

static void test_sorting4() {
    svector<unsigned> in;
    in.resize(5);
    test_sorting4_r(0, in);
    in.resize(8);
    test_sorting4_r(0, in);
}

void test_sorting3() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < 7; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    for (unsigned i = 0; i < in.size(); ++i) {
        std::cout << mk_pp(in[i].get(), m) << "\n";
    }
    ast_ext aext(m);
    sorting_network<ast_ext> sn(aext);
    sn(in, out);
    std::cout << "size: " << out.size() << "\n";
    for (unsigned i = 0; i < out.size(); ++i) {
        std::cout << mk_pp(out[i].get(), m) << "\n";
    }
}


struct ast_ext2 {
    ast_manager& m;
    expr_ref_vector m_clauses;
    expr_ref_vector m_trail;
    ast_ext2(ast_manager& m):m(m), m_clauses(m), m_trail(m) {}
    typedef expr* literal;
    typedef ptr_vector<expr> literal_vector;

    expr* trail(expr* e) {
        m_trail.push_back(e);
        return e;
    }

    literal mk_false() { return m.mk_false(); }
    literal mk_true() { return m.mk_true(); }
    literal mk_max(literal a, literal b) {
        return trail(m.mk_or(a, b));
    }
    literal mk_min(literal a, literal b) { return trail(m.mk_and(a, b)); }
    literal mk_not(literal a) { if (m.is_not(a,a)) return a;
        return trail(m.mk_not(a));
    }
    std::ostream& pp(std::ostream& out, literal lit) {
        return out << mk_pp(lit, m);
    }
    literal fresh() {
        return trail(m.mk_fresh_const("x", m.mk_bool_sort()));
    }
    void mk_clause(unsigned n, literal const* lits) {
        m_clauses.push_back(mk_or(m, n, lits));
    }
};


static void test_sorting_eq(unsigned n, unsigned k) {
    SASSERT(k < n);
    ast_manager m;
    reg_decl_plugins(m);
    ast_ext2 ext(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < n; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    smt_params fp;
    smt::kernel solver(m, fp);
    psort_nw<ast_ext2> sn(ext);
    expr_ref result(m);

    // equality:
    std::cout << "eq " << k << "\n";
    solver.push();
    result = sn.eq(true, k, in.size(), in.c_ptr());
    solver.assert_expr(result);
    for (unsigned i = 0; i < ext.m_clauses.size(); ++i) {
        solver.assert_expr(ext.m_clauses[i].get());
    }
    lbool res = solver.check();
    SASSERT(res == l_true);

    solver.push();
    for (unsigned i = 0; i < k; ++i) {
        solver.assert_expr(in[i].get());
    }
    res = solver.check();
    SASSERT(res == l_true);
    solver.assert_expr(in[k].get());
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formulas()[i], m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    SASSERT(res == l_false);
    solver.pop(1);
    ext.m_clauses.reset();
}

static void test_sorting_le(unsigned n, unsigned k) {
    ast_manager m;
    reg_decl_plugins(m);
    ast_ext2 ext(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < n; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    smt_params fp;
    smt::kernel solver(m, fp);
    psort_nw<ast_ext2> sn(ext);
    expr_ref result(m);
    // B <= k
    std::cout << "le " << k << "\n";
    solver.push();
    result = sn.le(false, k, in.size(), in.c_ptr());
    solver.assert_expr(result);
    for (unsigned i = 0; i < ext.m_clauses.size(); ++i) {
        solver.assert_expr(ext.m_clauses[i].get());
    }
    lbool res = solver.check();
    SASSERT(res == l_true);

    for (unsigned i = 0; i < k; ++i) {
        solver.assert_expr(in[i].get());
    }
    res = solver.check();
    SASSERT(res == l_true);
    solver.assert_expr(in[k].get());
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formulas()[i], m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    SASSERT(res == l_false);
    solver.pop(1);
    ext.m_clauses.reset();
}


void test_sorting_ge(unsigned n, unsigned k) {
    ast_manager m;
    reg_decl_plugins(m);
    ast_ext2 ext(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < n; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    smt_params fp;
    smt::kernel solver(m, fp);
    psort_nw<ast_ext2> sn(ext);
    expr_ref result(m);
    // k <= B
    std::cout << "ge " << k << "\n";
    solver.push();
    result = sn.ge(false, k, in.size(), in.c_ptr());
    solver.assert_expr(result);
    for (unsigned i = 0; i < ext.m_clauses.size(); ++i) {
        solver.assert_expr(ext.m_clauses[i].get());
    }
    lbool res = solver.check();
    SASSERT(res == l_true);

    solver.push();
    for (unsigned i = 0; i < n - k; ++i) {
        solver.assert_expr(m.mk_not(in[i].get()));
    }
    res = solver.check();
    SASSERT(res == l_true);
    solver.assert_expr(m.mk_not(in[n - k].get()));
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formulas()[i], m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    SASSERT(res == l_false);
    solver.pop(1);
}

void test_sorting5(unsigned n, unsigned k) {
    std::cout << "n: " << n << " k: " << k << "\n";
    test_sorting_le(n, k);
    test_sorting_eq(n, k);
    test_sorting_ge(n, k);
}

expr_ref naive_at_most1(expr_ref_vector const& xs) {
    ast_manager& m = xs.get_manager();
    expr_ref_vector clauses(m);
    for (unsigned i = 0; i < xs.size(); ++i) {
        for (unsigned j = i + 1; j < xs.size(); ++j) {
            clauses.push_back(m.mk_not(m.mk_and(xs[i], xs[j])));
        }
    }
    return mk_and(clauses);
}

void test_at_most_1(unsigned n, bool full) {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < n; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }

    ast_ext2 ext(m);
    psort_nw<ast_ext2> sn(ext);
    expr_ref result1(m), result2(m);
    result1 = sn.le(full, 1, in.size(), in.c_ptr());
    result2 = naive_at_most1(in);

    std::cout << "clauses: " << ext.m_clauses << "\n-----\n";

    smt_params fp;
    smt::kernel solver(m, fp);
    for (unsigned i = 0; i < ext.m_clauses.size(); ++i) {
        solver.assert_expr(ext.m_clauses[i].get());
    }
    lbool res;
    if (full) {
        solver.push();
        solver.assert_expr(m.mk_not(m.mk_eq(result1, result2)));

        std::cout << result1 << "\n";

        res = solver.check();
        SASSERT(res == l_false);

        solver.pop(1);
    }

    if (n >= 9) return;
    for (unsigned i = 0; i < static_cast<unsigned>(1 << n); ++i) {
        std::cout << "checking: " << n << ": " << i << "\n";
        solver.push();
        unsigned k = 0;
        for (unsigned j = 0; j < n; ++j) {
            bool is_true = (i & (1 << j)) != 0;
            expr_ref atom(m);
            atom = is_true ? in[j].get() : m.mk_not(in[j].get());
            solver.assert_expr(atom);
            std::cout << atom << "\n";
            if (is_true) ++k;
        }
        res = solver.check();
        SASSERT(res == l_true);
        if (k > 1) {
            solver.assert_expr(result1);
        }
        else if (!full) {
            solver.pop(1);
            continue;
        }
        else {
            solver.assert_expr(m.mk_not(result1));
        }
        res = solver.check();
        SASSERT(res == l_false);
        solver.pop(1);
    }
}


static void test_at_most1() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < 5; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    in[4] = in[3].get();

    ast_ext2 ext(m);
    psort_nw<ast_ext2> sn(ext);
    expr_ref result(m);
    result = sn.le(true, 1, in.size(), in.c_ptr());
    std::cout << result << "\n";
    std::cout << ext.m_clauses << "\n";
}

void tst_sorting_network() {
    for (unsigned i = 1; i < 17; ++i) {
        test_at_most_1(i, true);
        test_at_most_1(i, false);
    }
    test_at_most1();

    test_sorting_eq(11,7);
    for (unsigned n = 3; n < 20; n += 2) {
        for (unsigned k = 1; k < n; ++k) {
            test_sorting5(n, k);
        }
    }
    test_sorting1();
    test_sorting2();
    test_sorting3();
    test_sorting4();
}
