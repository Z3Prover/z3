
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "util/trace.h"
#include "util/vector.h"
#include "util/sorting_network.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/ast_util.h"
#include "model/model_smt2_pp.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"

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
        return nullptr;
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
        ENSURE(v[i] <= v[i+1]);
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
    for (expr* e : in) std::cout << mk_pp(e, m) << "\n";
    ast_ext aext(m);
    sorting_network<ast_ext> sn(aext);
    sn(in, out);
    std::cout << "size: " << out.size() << "\n";
    for (expr* e : out) std::cout << mk_pp(e, m) << "\n";
}


struct ast_ext2 {
    ast_manager& m;
    expr_ref_vector m_clauses;
    expr_ref_vector m_trail;
    ast_ext2(ast_manager& m):m(m), m_clauses(m), m_trail(m) {}
    typedef expr* pliteral;
    typedef ptr_vector<expr> pliteral_vector;

    expr* trail(expr* e) {
        m_trail.push_back(e);
        return e;
    }

    pliteral mk_false() { return m.mk_false(); }
    pliteral mk_true() { return m.mk_true(); }
    pliteral mk_max(unsigned n, pliteral const* lits) {
        return trail(m.mk_or(n, lits));
    }
    pliteral mk_min(unsigned n, pliteral const* lits) {
        return trail(m.mk_and(n, lits));
    }
    pliteral mk_not(pliteral a) { if (m.is_not(a,a)) return a;
        return trail(m.mk_not(a));
    }
    std::ostream& pp(std::ostream& out, pliteral lit) {
        return out << mk_pp(lit, m);
    }
    pliteral fresh(char const* n) {
        return trail(m.mk_fresh_const(n, m.mk_bool_sort()));
    }
    void mk_clause(unsigned n, pliteral const* lits) {
        m_clauses.push_back(mk_or(m, n, lits));
    }
};

static void test_eq1(unsigned n, sorting_network_encoding enc) {
    //std::cout << "test eq1 " << n << " for encoding: " << enc << "\n";
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
    sn.cfg().m_encoding = enc;

    expr_ref result1(m), result2(m);

    // equality:
    solver.push();
    result1 = sn.eq(true, 1, in.size(), in.data());
    for (expr* cls : ext.m_clauses) {
        solver.assert_expr(cls);
    }
    expr_ref_vector ors(m);
    for (unsigned i = 0; i < n; ++i) {
        expr_ref_vector ands(m);
        for (unsigned j = 0; j < n; ++j) {
            ands.push_back(j == i ? in[j].get() : m.mk_not(in[j].get()));
        }
        ors.push_back(mk_and(ands));
    }
    result2 = mk_or(ors);
    solver.assert_expr(m.mk_not(m.mk_eq(result1, result2)));
    //std::cout << ext.m_clauses << "\n";
    //std::cout << result1 << "\n";
    //std::cout << result2 << "\n";
    lbool res = solver.check();
    if (res == l_true) {
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    ENSURE(l_false == res);
    ext.m_clauses.reset();
}

static void test_sorting_eq(unsigned n, unsigned k, sorting_network_encoding enc) {
    ENSURE(k < n);
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
    sn.cfg().m_encoding = enc;
    expr_ref result(m);

    // equality:
    std::cout << "eq " << k << " out of " << n << " for encoding " << enc << "\n";
    solver.push();
    result = sn.eq(false, k, in.size(), in.data());
    solver.assert_expr(result);
    for (expr* cl : ext.m_clauses) {
        solver.assert_expr(cl);
    }
    lbool res = solver.check();
    if (res != l_true) {
        std::cout << res << "\n";
        solver.display(std::cout);
    }
    ENSURE(res == l_true);

    solver.push();
    for (unsigned i = 0; i < k; ++i) {
        solver.assert_expr(in[i].get());
    }
    res = solver.check();
    if (res != l_true) {
        std::cout << result << "\n" << ext.m_clauses << "\n";
    }
    ENSURE(res == l_true);
    solver.assert_expr(in[k].get());
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formula(i), m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    ENSURE(res == l_false);
    solver.pop(1);
    ext.m_clauses.reset();
}

static void test_sorting_le(unsigned n, unsigned k, sorting_network_encoding enc) {
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
    sn.cfg().m_encoding = enc;
    expr_ref result(m);
    // B <= k
    std::cout << "le " << k << "\n";
    solver.push();
    result = sn.le(false, k, in.size(), in.data());
    solver.assert_expr(result);
    for (expr* cls : ext.m_clauses) {
        solver.assert_expr(cls);
    }
    lbool res = solver.check();
    if (res != l_true) {
        std::cout << res << "\n";
        solver.display(std::cout);
        std::cout << "clauses: " << ext.m_clauses << "\n";
        std::cout << "result: " << result << "\n";
    }
    ENSURE(res == l_true);

    for (unsigned i = 0; i < k; ++i) {
        solver.assert_expr(in[i].get());
    }
    res = solver.check();
    if (res != l_true) {
        std::cout << res << "\n";
        solver.display(std::cout);
    }
    ENSURE(res == l_true);
    solver.assert_expr(in[k].get());
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formula(i), m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    ENSURE(res == l_false);
    solver.pop(1);
    ext.m_clauses.reset();
}


void test_sorting_ge(unsigned n, unsigned k, sorting_network_encoding enc) {
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
    sn.cfg().m_encoding = enc;
    expr_ref result(m);
    // k <= B
    std::cout << "ge " << k << "\n";
    solver.push();
    result = sn.ge(false, k, in.size(), in.data());
    solver.assert_expr(result);
    for (expr* cls : ext.m_clauses) {
        solver.assert_expr(cls);
    }
    lbool res = solver.check();
    ENSURE(res == l_true);

    solver.push();
    for (unsigned i = 0; i < n - k; ++i) {
        solver.assert_expr(m.mk_not(in[i].get()));
    }
    res = solver.check();
    ENSURE(res == l_true);
    solver.assert_expr(m.mk_not(in[n - k].get()));
    res = solver.check();
    if (res == l_true) {
        TRACE("pb",
              unsigned sz = solver.size();
              for (unsigned i = 0; i < sz; ++i) {
                  tout << mk_pp(solver.get_formula(i), m) << "\n";
              });
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        TRACE("pb", model_smt2_pp(tout, m, *model, 0););
    }
    ENSURE(res == l_false);
    solver.pop(1);
}

void test_sorting5(unsigned n, unsigned k, sorting_network_encoding enc) {
    std::cout << "n: " << n << " k: " << k << "\n";
    test_sorting_le(n, k, enc);
    test_sorting_eq(n, k, enc);
    test_sorting_ge(n, k, enc);
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

void test_at_most_1(unsigned n, bool full, sorting_network_encoding enc) {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < n; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }

    ast_ext2 ext(m);
    psort_nw<ast_ext2> sn(ext);
    sn.cfg().m_encoding = enc;
    expr_ref result1(m), result2(m);
    result1 = sn.le(full, 1, in.size(), in.data());
    result2 = naive_at_most1(in);


    std::cout << "clauses: " << ext.m_clauses << "\n-----\n";
    //std::cout << "encoded: " << result1 << "\n";
    //std::cout << "naive: " << result2 << "\n";

    smt_params fp;
    smt::kernel solver(m, fp);
    for (expr* cls : ext.m_clauses) {
        solver.assert_expr(cls);
    }
    if (full) {
        solver.push();
        solver.assert_expr(m.mk_not(m.mk_eq(result1, result2)));

        std::cout << result1 << "\n";
        lbool res = solver.check();
        if (res == l_true) {
            model_ref model;
            solver.get_model(model);
            model_smt2_pp(std::cout, m, *model, 0);            
        }

        VERIFY(l_false == res);

        solver.pop(1);
    }

    if (n >= 9) return;
    if (n <= 1) return;
    for (unsigned i = 0; i < static_cast<unsigned>(1 << n); ++i) {
        std::cout << "checking n: " << n << " bits: ";
        for (unsigned j = 0; j < n; ++j) {
            bool is_true = (i & (1 << j)) != 0;
            std::cout << (is_true?"1":"0");
        }
        std::cout << "\n";
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
        VERIFY(l_false == solver.check());
        solver.pop(1);
    }
}


static void test_at_most1(sorting_network_encoding enc) {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector in(m), out(m);
    for (unsigned i = 0; i < 5; ++i) {
        in.push_back(m.mk_fresh_const("a",m.mk_bool_sort()));
    }
    in[4] = in[3].get();

    ast_ext2 ext(m);
    psort_nw<ast_ext2> sn(ext);
    sn.cfg().m_encoding = enc;
    expr_ref result(m);
    result = sn.le(true, 1, in.size(), in.data());
    //std::cout << result << "\n";
    //std::cout << ext.m_clauses << "\n";
}

static void test_sorting5(sorting_network_encoding enc) {
    test_sorting_eq(11,7, enc);
    for (unsigned n = 3; n < 20; n += 2) {
        for (unsigned k = 1; k < n; ++k) {
            test_sorting5(n, k, enc);
        }
    }
}

static void tst_sorting_network(sorting_network_encoding enc) {
    for (unsigned i = 1; i < 17; ++i) {
        test_at_most_1(i, true, enc);
        test_at_most_1(i, false, enc);
    }
    for (unsigned n = 2; n < 20; ++n) {
        std::cout << "verify eq-1 out of " << n << "\n";
        test_sorting_eq(n, 1, enc);
        test_eq1(n, enc);
    }
    test_at_most1(enc);
    test_sorting5(enc);
}

static void test_pb(unsigned max_w, unsigned sz, unsigned_vector& ws) {
    if (ws.empty()) {
        for (unsigned w = 1; w <= max_w; ++w) {
            ws.push_back(w);
            test_pb(max_w, sz, ws);
            ws.pop_back();
        }        
    }
    else if (ws.size() < sz) {
        for (unsigned w = ws.back(); w <= max_w; ++w) {
            ws.push_back(w);
            test_pb(max_w, sz, ws);
            ws.pop_back();
        }        
    }
    else {
        SASSERT(ws.size() == sz);
        ast_manager m;
        reg_decl_plugins(m);
        expr_ref_vector xs(m), nxs(m);
        expr_ref ge(m), eq(m);
        smt_params fp;
        smt::kernel solver(m, fp);
        for (unsigned i = 0; i < sz; ++i) {
            xs.push_back(m.mk_const(symbol(i), m.mk_bool_sort()));
            nxs.push_back(m.mk_not(xs.back()));
        }
        std::cout << ws << " " << "\n";
        for (unsigned k = max_w + 1; k < ws.size()*max_w; ++k) {

            ast_ext2 ext(m);
            psort_nw<ast_ext2> sn(ext);
            solver.push();
            //std::cout << "bound: " << k << "\n";
            //std::cout << ws << " " << xs << "\n";
            ge = sn.ge(k, sz, ws.data(), xs.data());
            //std::cout << "ge: " << ge << "\n";            
            for (expr* cls : ext.m_clauses) {
                solver.assert_expr(cls);
            }
            // solver.display(std::cout);
            // for each truth assignment to xs, validate 
            // that circuit computes the right value for ge
            for (unsigned i = 0; i < (1ul << sz); ++i) {
                solver.push();
                unsigned sum = 0;
                for (unsigned j = 0; j < sz; ++j) {
                    if (0 == ((1 << j) & i)) {
                        solver.assert_expr(xs.get(j));
                        sum += ws[j];
                    }
                    else {
                        solver.assert_expr(nxs.get(j));
                    }
                }
                // std::cout << "bound: " << k << "\n";
                // std::cout << ws << " " << xs << "\n";
                // std::cout << sum << " >= " << k << " : " << (sum >= k) << " ";
                solver.push();
                if (sum < k) {
                    solver.assert_expr(m.mk_not(ge));
                }
                else {
                    solver.assert_expr(ge);
                }
                // solver.display(std::cout) << "\n";
                VERIFY(solver.check() == l_true);
                solver.pop(1);

                solver.push();
                if (sum >= k) {
                    solver.assert_expr(m.mk_not(ge));
                }
                else {
                    solver.assert_expr(ge);
                }
                // solver.display(std::cout) << "\n";
                VERIFY(l_false == solver.check());
                solver.pop(1);
                solver.pop(1);
            }            
            solver.pop(1);

            solver.push();
            eq = sn.eq(k, sz, ws.data(), xs.data());

            for (expr* cls : ext.m_clauses) {
                solver.assert_expr(cls);
            }
            // for each truth assignment to xs, validate 
            // that circuit computes the right value for ge
            for (unsigned i = 0; i < (1ul << sz); ++i) {
                solver.push();
                unsigned sum = 0;
                for (unsigned j = 0; j < sz; ++j) {
                    if (0 == ((1 << j) & i)) {
                        solver.assert_expr(xs.get(j));
                        sum += ws[j];
                    }
                    else {
                        solver.assert_expr(nxs.get(j));
                    }
                }
                solver.push();
                if (sum != k) {
                    solver.assert_expr(m.mk_not(eq));
                }
                else {
                    solver.assert_expr(eq);
                }
                // solver.display(std::cout) << "\n";
                VERIFY(solver.check() == l_true);
                solver.pop(1);

                solver.push();
                if (sum == k) {
                    solver.assert_expr(m.mk_not(eq));
                }
                else {
                    solver.assert_expr(eq);
                }
                VERIFY(l_false == solver.check());
                solver.pop(1);
                solver.pop(1);
            }            
            
            solver.pop(1);
        }
    }
}

static void tst_pb() {
    unsigned_vector ws;
    test_pb(3, 3, ws);
}

void tst_sorting_network() {
    tst_pb();
    tst_sorting_network(sorting_network_encoding::unate_at_most);
    tst_sorting_network(sorting_network_encoding::circuit_at_most);
    tst_sorting_network(sorting_network_encoding::ordered_at_most);
    tst_sorting_network(sorting_network_encoding::grouped_at_most);
    tst_sorting_network(sorting_network_encoding::bimander_at_most);
    test_sorting1();
    test_sorting2();
    test_sorting3();
    test_sorting4();
}

