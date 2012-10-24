#include "ast.h"
#include "front_end_params.h"
#include "qe.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "lbool.h"
#include <sstream>
#include "expr_replacer.h"
#include "smt_solver.h"
#include "reg_decl_plugins.h"

static void validate_quant_solution(ast_manager& m, app* x, expr* fml, expr* t, expr* new_fml) {
    // verify:
    //    new_fml <=> fml[t/x]
    scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
    expr_substitution sub(m);
    sub.insert(x, t);
    rep->set_substitution(&sub);
    expr_ref fml1(fml, m);
    (*rep)(fml1);
    expr_ref tmp(m);
    tmp = m.mk_not(m.mk_iff(new_fml, fml1));
    front_end_params fp;
    smt::solver solver(m, fp);
    solver.assert_expr(tmp);
    lbool res = solver.check();
    std::cout << res << "\n";
    SASSERT(res == l_false);
}

static void test_quant_solver(ast_manager& m, app* x, expr* fml) {
    front_end_params params;
    params.m_quant_elim = true;
    qe::expr_quant_elim qe(m, params);
    expr_ref_vector terms(m);
    expr_ref_vector fmls(m);
    bool success = qe.solve_for_var(x, fml, terms, fmls);
    std::cout << "------------------------\n";
    std::cout << mk_pp(fml, m) << "\n";
    if (success) {
        for (unsigned i = 0; i < terms.size(); ++i) {
            std::cout << mk_pp(x, m) << " = " << mk_pp(terms[i].get(), m) << "\n" << mk_pp(fmls[i].get(), m) << "\n";
            validate_quant_solution(m, x, fml, terms[i].get(), fmls[i].get());
        }
    }
    else {
        std::cout << "failed\n";
    }
}

static void test_quant_solver_rec(ast_manager& m, unsigned num_vars, app* const* xs, expr* fml) {
    if (num_vars == 0) {
        return;
    }
    front_end_params params;
    params.m_quant_elim = true;
    qe::expr_quant_elim qe(m, params);
    expr_ref_vector fmls(m), ors(m), terms(m);
    app* x = xs[0];
    bool success = qe.solve_for_var(x, fml, terms, fmls);
    std::cout << "------------------------\n";
    std::cout << mk_pp(fml, m) << "\n";
    if (success) {
        for (unsigned i = 0; i < terms.size(); ++i) {
            std::cout << mk_pp(x, m) << " = " << mk_pp(terms[i].get(), m) << "\n" << mk_pp(fmls[i].get(), m) << "\n";
            validate_quant_solution(m, x, fml, terms[i].get(), fmls[i].get());
            ors.reset();
            if (m.is_or(fmls[i].get())) {
                ors.append(to_app(fmls[i].get())->get_num_args(), to_app(fmls[i].get())->get_args());
            }
            else {
                ors.push_back(fmls[i].get());
            }
            for (unsigned j = 0; j < ors.size(); ++j) {
                test_quant_solver_rec(m, num_vars-1, xs+1, ors[j].get());
            }
        }
    }
    else {
        std::cout << "failed\n";
    }
}



static void test_quant_solve1() {
    ast_manager m;
    arith_util ar(m);

    reg_decl_plugins(m);
    sort* i = ar.mk_int();
    app_ref x(m.mk_const(symbol("x"),i), m);
    app_ref y(m.mk_const(symbol("y"),i), m);
    app_ref a(m.mk_const(symbol("a"),i), m);
    app_ref b(m.mk_const(symbol("b"),i), m);
    expr_ref n2(ar.mk_numeral(rational(2), true), m);
    expr_ref n3(ar.mk_numeral(rational(3), true), m);
    expr_ref n4(ar.mk_numeral(rational(4), true), m);
    expr_ref n10(ar.mk_numeral(rational(10), true), m);
    expr_ref n20(ar.mk_numeral(rational(20), true), m);
    expr_ref x2(ar.mk_mul(n2, x), m);
    expr_ref x3(ar.mk_mul(n3, x), m);
    expr_ref fml1(m), fml2(m), fml3(m), fml4(m);
    expr_ref fml(m), t1(m), t2(m);

    fml1 = m.mk_eq(x, a);
    fml2 = ar.mk_lt(x, a);
    fml3 = ar.mk_gt(x, a);
    fml4 = m.mk_and(ar.mk_lt(x, a), ar.mk_lt(x, b));
    expr_ref fml5(m.mk_and(ar.mk_gt(x, a), ar.mk_lt(x, b)), m);
    expr_ref fml6(ar.mk_le(x, a), m);
    expr_ref fml7(ar.mk_ge(x, a), m);
    expr_ref fml8(ar.mk_lt(ar.mk_mul(n2, x), a), m);
    expr_ref fml9(m.mk_eq(ar.mk_mul(n2, x), a), m);

    test_quant_solver(m, x.get(), fml1.get());
    test_quant_solver(m, x.get(), fml2.get());
    test_quant_solver(m, x.get(), fml3.get());
    test_quant_solver(m, x.get(), fml4.get());
    test_quant_solver(m, x.get(), fml5.get());
    test_quant_solver(m, x.get(), fml6.get());
    test_quant_solver(m, x.get(), fml7.get());
    test_quant_solver(m, x.get(), fml8.get());
    test_quant_solver(m, x.get(), fml9.get());

    fml = ar.mk_lt(x2, a); test_quant_solver(m, x.get(), fml.get());
    fml = ar.mk_gt(x2, a); test_quant_solver(m, x.get(), fml.get());
    fml = ar.mk_le(x2, a); test_quant_solver(m, x.get(), fml.get());
    fml = ar.mk_ge(x2, a); test_quant_solver(m, x.get(), fml.get());


    fml = m.mk_and(ar.mk_lt(a, ar.mk_mul(n3,x)), ar.mk_lt(ar.mk_mul(n3,x), b));
    test_quant_solver(m, x.get(), fml.get());

    t1 = ar.mk_sub(ar.mk_mul(n2,y),b);
    t2 = ar.mk_add(ar.mk_mul(n3,x),a);
    fml1 = ar.mk_le(t1, t2);
    t1 = ar.mk_sub(ar.mk_mul(n2,x),a);
    t2 = ar.mk_add(ar.mk_mul(n4,y),b);
    fml2 = ar.mk_le(t1,t2);
    fml = m.mk_and(fml1, fml2);
    app* xy[2] = { x.get(), y.get() };
    test_quant_solver_rec(m, 2, xy, fml.get());
}


void tst_quant_solve() {

    test_quant_solve1();   

    memory::finalize();
#ifdef _WINDOWS
    _CrtDumpMemoryLeaks();
#endif
    exit(0);
}


