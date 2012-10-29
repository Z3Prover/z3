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
#include "smtparser.h"
#include "expr_abstract.h"
#include "model_smt2_pp.h"

static void validate_quant_solution(ast_manager& m, expr* fml, expr* guard, qe::def_vector const& defs) {
    // verify:
    //    new_fml => fml[t/x]
    scoped_ptr<expr_replacer> rep = mk_expr_simp_replacer(m);
    app_ref_vector xs(m);
    expr_substitution sub(m);
    for (unsigned i = 0; i < defs.size(); ++i) {
        xs.push_back(m.mk_const(defs.var(i)));
        sub.insert(xs.back(), defs.def(i));
    }
    rep->set_substitution(&sub);
    expr_ref fml1(fml, m);
    (*rep)(fml1);
    expr_ref tmp(m);
    tmp = m.mk_not(m.mk_implies(guard, fml1));
    front_end_params fp;
    smt::solver solver(m, fp);
    solver.assert_expr(tmp);
    lbool res = solver.check();
    //SASSERT(res == l_false);
    if (res != l_false) {
        std::cout << "Validation failed: " << res << "\n";
        std::cout << mk_pp(tmp, m) << "\n";
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        fatal_error(0);
    }
}


static void validate_quant_solutions(app* x, expr* fml, expr_ref_vector& guards) {
    return;
    // quant_elim option got removed...
    // verify:
    //    fml <=> guard_1 \/ guard_2 \/ ... 
    ast_manager& m = guards.get_manager();
    expr_ref tmp(m), fml2(m);
    tmp = m.mk_or(guards.size(), guards.c_ptr());
    expr* _x = x;
    std::cout << mk_pp(fml, m) << "\n";
    expr_abstract(m, 0, 1, &_x, fml, fml2);
    std::cout << mk_pp(fml2, m) << "\n";
    symbol name(x->get_decl()->get_name());
    sort* s = m.get_sort(x);
    fml2 = m.mk_exists(1, &s, &name, fml2);
    std::cout << mk_pp(fml2, m) << "\n";
    tmp = m.mk_not(m.mk_iff(fml2, tmp));
    std::cout << mk_pp(tmp, m) << "\n";
    front_end_params fp;
    smt::solver solver(m, fp);
    solver.assert_expr(tmp);
    lbool res = solver.check();
    std::cout << "checked\n";
    SASSERT(res == l_false);
    if (res != l_false) {
        std::cout << res << "\n";
        fatal_error(0);
    }
}

static void test_quant_solver(ast_manager& m, app* x, expr* fml) {
    front_end_params params;
    qe::expr_quant_elim qe(m, params);
    qe::guarded_defs defs(m);
    bool success = qe.solve_for_var(x, fml, defs);
    std::cout << "------------------------\n";
    std::cout << mk_pp(fml, m) << "\n";
    if (success) {        
        defs.display(std::cout);
        for (unsigned i = 0; i < defs.size(); ++i) {     
            validate_quant_solution(m, fml, defs.guard(i), defs.defs(i));
        }
    }
    else {
        std::cout << "failed\n";
    }
}


static void test_quant_solver(ast_manager& m, unsigned sz, app*const* xs, expr* fml) {
    front_end_params params;
    qe::expr_quant_elim qe(m, params);
    qe::guarded_defs defs(m);
    bool success = qe.solve_for_vars(sz, xs, fml, defs);
    std::cout << "------------------------\n";
    std::cout << mk_pp(fml, m) << "\n";
    if (success) {        
        defs.display(std::cout);
        for (unsigned i = 0; i < defs.size(); ++i) {     
            validate_quant_solution(m, fml, defs.guard(i), defs.defs(i));
        }
    }
    else {
        std::cout << "failed\n";
    }
}


static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    reg_decl_plugins(m);    
    scoped_ptr<smtlib::parser> parser = smtlib::parser::create(m);
    parser->initialize_smtlib();
    std::ostringstream buffer;
    buffer << "(benchmark presburger :status unknown :logic AUFLIA "
           << ":extrafuns ((x Int) (y Int) (z Int) (a Int) (b Int))\n"
           << ":formula " << str << ")";
    parser->parse_string(buffer.str().c_str());
    smtlib::benchmark* b = parser->get_benchmark();
    smtlib::theory::expr_iterator it  = b->begin_formulas();
    smtlib::theory::expr_iterator end = b->end_formulas();
    SASSERT(it != b->end_formulas());
    result = *it;
    return result;
}

static void test_quant_solver(ast_manager& m, app* x, char const* str) {
    expr_ref fml = parse_fml(m, str);
    test_quant_solver(m, x, fml);
}

static void test_quant_solver(ast_manager& m, unsigned sz, app*const* xs, char const* str) {
    expr_ref fml = parse_fml(m, str);
    test_quant_solver(m, sz, xs, fml);
}



static void test_quant_solve1() {
    ast_manager m;
    arith_util ar(m);
    reg_decl_plugins(m);
    sort* i = ar.mk_int();
    app_ref xr(m.mk_const(symbol("x"),i), m);
    app_ref yr(m.mk_const(symbol("y"),i), m);
    app* x = xr.get();
    app* y = yr.get();
    app* xy[2] = { x, y };


    test_quant_solver(m, x, "(and (<= x y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (<= (* 2 x) y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (>= x y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (>= (* 2 x) y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (<= (* 2 x) y) (>= x z) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (<= (* 2 x) y) (>= (* 3 x) z) (= (mod x 2) 0))");

    test_quant_solver(m, x, "(>= (* 2 x) a)");

    test_quant_solver(m, x, "(<= (* 2 x) a)");
    test_quant_solver(m, x, "(< (* 2 x) a)");
    test_quant_solver(m, x, "(= (* 2 x) a)");
    test_quant_solver(m, x, "(< (* 2 x) a)");
    test_quant_solver(m, x, "(> (* 2 x) a)");


    test_quant_solver(m, x, "(and (<= a x) (<= (* 2 x) b))");

    test_quant_solver(m, x, "(and (<= a x) (<= x b))");
    test_quant_solver(m, x, "(and (<= (* 2 a) x) (<= x b))");
    test_quant_solver(m, x, "(and (<= (* 2 a) x) (<= (* 2 x) b))");
    test_quant_solver(m, x, "(and (<= a x) (<= (* 3 x) b))");
    test_quant_solver(m, x, "(and (<= (* 3 a) x) (<= x b))");
    test_quant_solver(m, x, "(and (<= (* 3 a) x) (<= (* 3 x) b))");

    test_quant_solver(m, x, "(and (< a (* 3 x)) (< (* 3 x) b))");    

    test_quant_solver(m, x, "(< (* 3 x) a)");
    test_quant_solver(m, x, "(= (* 3 x) a)");
    test_quant_solver(m, x, "(< (* 3 x) a)");
    test_quant_solver(m, x, "(> (* 3 x) a)");
    test_quant_solver(m, x, "(<= (* 3 x) a)");
    test_quant_solver(m, x, "(>= (* 3 x) a)");

    test_quant_solver(m, x, "(<= (* 2 x) a)");
    test_quant_solver(m, x, "(or (= (* 2 x) y) (= (+ (* 2 x) 1) y))");
    test_quant_solver(m, x, "(= x a)");
    test_quant_solver(m, x, "(< x a)");
    test_quant_solver(m, x, "(> x a)");
    test_quant_solver(m, x, "(and (> x a) (< x b))");
    test_quant_solver(m, x, "(and (> x a) (< x b))");
    test_quant_solver(m, x, "(<= x a)");
    test_quant_solver(m, x, "(>= x a)");
    test_quant_solver(m, x, "(and (<= (* 2 x) y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(= (* 2 x) y)");
    test_quant_solver(m, x, "(or (< x 0) (> x 1))");
    test_quant_solver(m, x, "(or (< x y) (> x y))");
    test_quant_solver(m, x, "(= x y)");
    test_quant_solver(m, x, "(<= x y)");
    test_quant_solver(m, x, "(>= x y)");
    test_quant_solver(m, x, "(and (<= (+ x y) 0) (<= (+ x z) 0))");
    test_quant_solver(m, x, "(and (<= (+ x y) 0) (<= (+ (* 2 x) z) 0))");
    test_quant_solver(m, x, "(and (<= (+ (* 3 x) y) 0) (<= (+ (* 2 x) z) 0))");
    test_quant_solver(m, x, "(and (>= x y) (>= x z))");
    test_quant_solver(m, x, "(< x y)");
    test_quant_solver(m, x, "(> x y)");

    test_quant_solver(m, 2, xy, "(and (<= (- (* 2 y) b) (+ (* 3 x) a)) (<= (- (* 2 x) a) (+ (* 4 y) b)))");

}


void tst_quant_solve() {

    test_quant_solve1();   

    memory::finalize();
#ifdef _WINDOWS
    _CrtDumpMemoryLeaks();
#endif
    exit(0);
}


