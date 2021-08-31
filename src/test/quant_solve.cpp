
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/ast.h"
#include "smt/params/smt_params.h"
#include "qe/qe.h"
#include "ast/arith_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/lbool.h"
#include <sstream>
#include "ast/rewriter/expr_replacer.h"
#include "smt/smt_kernel.h"
#include "ast/reg_decl_plugins.h"
#include "ast/expr_abstract.h"
#include "model/model_smt2_pp.h"
#include "parsers/smt2/smt2parser.h"
#include "ast/rewriter/var_subst.h"

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
    std::cout << "validating: " << mk_pp(tmp, m) << "\n";
    smt_params fp;
    smt::kernel solver(m, fp);
    solver.assert_expr(tmp);
    lbool res = solver.check();
    //ENSURE(res == l_false);
    if (res != l_false) {
        std::cout << "Validation failed: " << res << "\n";
        std::cout << mk_pp(tmp, m) << "\n";
        model_ref model;
        solver.get_model(model);
        model_smt2_pp(std::cout, m, *model, 0);
        fatal_error(0);
    }
}


#if 0
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
    sort* s = x->get_sort();
    fml2 = m.mk_exists(1, &s, &name, fml2);
    std::cout << mk_pp(fml2, m) << "\n";
    tmp = m.mk_not(m.mk_iff(fml2, tmp));
    std::cout << mk_pp(tmp, m) << "\n";
    smt_params fp;
    smt::kernel solver(m, fp);
    solver.assert_expr(tmp);
    lbool res = solver.check();
    std::cout << "checked\n";
    ENSURE(res == l_false);
    if (res != l_false) {
        std::cout << res << "\n";
        fatal_error(0);
    }
}
#endif


static void test_quant_solver(ast_manager& m, unsigned sz, app*const* xs, expr* fml, bool validate) {
    smt_params params;
    qe::expr_quant_elim qe(m, params);
    qe::guarded_defs defs(m);
    bool success = qe.solve_for_vars(sz, xs, fml, defs);
    std::cout << "------------------------\n";
    std::cout << mk_pp(fml, m) << "\n";
    if (success) {        
        defs.display(std::cout);
        
        for (unsigned i = 0; validate && i < defs.size(); ++i) {     
            validate_quant_solution(m, fml, defs.guard(i), defs.defs(i));
        }
    }
    else {
        std::cout << "failed\n";
    }
}

static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Int)\n"
           << "(declare-const y Int)\n"
           << "(declare-const z Int)\n"
           << "(declare-const a Int)\n"
           << "(declare-const b Int)\n"
           << "(declare-const P Bool)\n"
           << "(declare-const Q Bool)\n"
           << "(declare-const r1 Real)\n"
           << "(declare-const r2 Real)\n"
           << "(declare-datatypes () ((IList (nil) (cons (car Int) (cdr IList)))))\n"
           << "(declare-const l1 IList)\n"
           << "(declare-const l2 IList)\n"
           << "(declare-datatypes () ((Cell (null) (cell (car Cell) (cdr Cell)))))\n"
           << "(declare-const c1 Cell)\n"
           << "(declare-const c2 Cell)\n"
           << "(declare-const c3 Cell)\n"
           << "(declare-datatypes () ((Tuple (tuple (first Int) (second Bool) (third Real)))))\n"
           << "(declare-const t1 Tuple)\n"
           << "(declare-const t2 Tuple)\n"
           << "(declare-const t3 Tuple)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    result = ctx.assertions().get(0);
    return result;
}


static void parse_fml(char const* str, app_ref_vector& vars, expr_ref& fml) {
    ast_manager& m = fml.get_manager();
    fml = parse_fml(m, str);
    if (is_exists(fml)) {
        quantifier* q = to_quantifier(fml);
        for (unsigned i = 0; i < q->get_num_decls(); ++i) {
            vars.push_back(m.mk_const(q->get_decl_name(i), q->get_decl_sort(i)));
        }
        fml = q->get_expr();
        var_subst vs(m, true);
        fml = vs(fml, vars.size(), (expr*const*)vars.data());
    }
}

static void test_quant_solver(ast_manager& m, app* x, char const* str, bool validate = true) {
    expr_ref fml = parse_fml(m, str);
    test_quant_solver(m, 1, &x, fml, validate);
}

static void test_quant_solver(ast_manager& m, unsigned sz, app*const* xs, char const* str, bool validate = true) {
    expr_ref fml = parse_fml(m, str);
    test_quant_solver(m, sz, xs, fml, validate);
}

static void test_quant_solver(ast_manager& m, char const* str, bool validate = true) {
    expr_ref fml(m);
    app_ref_vector vars(m);
    parse_fml(str, vars, fml);
    test_quant_solver(m, vars.size(), vars.data(), fml, validate);
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


    test_quant_solver(m, x, "(and (<= (* 2 x) y) (>= x z) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (<= x y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (<= (* 2 x) y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (>= x y) (= (mod x 2) 0))");
    test_quant_solver(m, x, "(and (>= (* 2 x) y) (= (mod x 2) 0))");
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

    test_quant_solver(m, "(exists ((c Cell)) (= c null))");
    test_quant_solver(m, "(exists ((c Cell)) (= c (cell null c1)))");

    test_quant_solver(m, "(exists ((c Cell)) (not (= c null)))", false);
    test_quant_solver(m, "(exists ((c Cell)) (= (cell c c) c1))", false);
    test_quant_solver(m, "(exists ((c Cell)) (= (cell c (cdr c1)) c1))", false);


    test_quant_solver(m, "(exists ((t Tuple)) (= (tuple a P r1) t))");
    test_quant_solver(m, "(exists ((t Tuple)) (= a (first t)))");
    test_quant_solver(m, "(exists ((t Tuple)) (= P (second t)))");
    test_quant_solver(m, "(exists ((t Tuple)) (= r2 (third t)))");
    test_quant_solver(m, "(exists ((t Tuple)) (not (= a (first t))))");
    test_quant_solver(m, "(exists ((t Tuple)) (not (= P (second t))))");
    test_quant_solver(m, "(exists ((t Tuple)) (not (= r2 (third t))))");
}


void tst_quant_solve() {
    disable_debug("heap");

    test_quant_solve1();   

#if 0
    memory::finalize();
#ifdef _WINDOWS
    _CrtDumpMemoryLeaks();
#endif
    exit(0);
#endif
}


