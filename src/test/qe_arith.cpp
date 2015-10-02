
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "qe_arith.h"
#include "qe.h"
#include "th_rewriter.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "arith_rewriter.h"
#include "ast_pp.h"
#include "qe_util.h"
#include "smt_context.h"
#include "expr_abstract.h"

static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Real)\n"
           << "(declare-const y Real)\n"
           << "(declare-const z Real)\n"
           << "(declare-const u Real)\n"
           << "(declare-const v Real)\n"
           << "(declare-const t Real)\n"
           << "(declare-const a Real)\n"
           << "(declare-const b Real)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* example1 = "(and (<= x 3.0) (<= (* 3.0 x) y) (<= z y))";
static char const* example2 = "(and (<= z x) (<= x 3.0) (<= (* 3.0 x) y) (<= z y))";
static char const* example3 = "(and (<= z x) (<= x 3.0) (< (* 3.0 x) y) (<= z y))";
static char const* example4 = "(and (<= z x) (<= x 3.0) (not (>= (* 3.0 x) y)) (<= z y))";
static char const* example5 = "(and (<= y x) (<= z x) (<= x u) (<= x v) (<= x t))";

static char const* example6 = "(and (<= 0 (+ x z))\
     (>= y x) \
     (<= y x)\
     (<= (- u y) 0.0)\
     (>= x (+ v z))\
     (>= x 0.0)\
     (<= x 1.0))";


static void test(char const *ex) {
    smt_params params;
    params.m_model = true;
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    app_ref_vector vars(m);
    expr_ref_vector lits(m);
    vars.push_back(m.mk_const(symbol("x"), a.mk_real()));
    flatten_and(fml, lits);

    smt::context ctx(m, params);
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    SASSERT(result == l_true);
    ref<model> md;
    ctx.get_model(md);    
    expr_ref pr = qe::arith_project(*md, vars, lits);
    
    std::cout << mk_pp(fml, m) << "\n";
    std::cout << mk_pp(pr, m) << "\n";
    
}

static void test2(char const *ex) {
    smt_params params;
    params.m_model = true;
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    app_ref_vector vars(m);
    expr_ref_vector lits(m);
    vars.push_back(m.mk_const(symbol("x"), a.mk_real()));
    vars.push_back(m.mk_const(symbol("y"), a.mk_real()));
    vars.push_back(m.mk_const(symbol("z"), a.mk_real()));
    flatten_and(fml, lits);

    smt::context ctx(m, params);
    ctx.push();
    ctx.assert_expr(fml);
    lbool result = ctx.check();
    SASSERT(result == l_true);
    ref<model> md;
    ctx.get_model(md);  
    ctx.pop(1);
    
    std::cout << mk_pp(fml, m) << "\n";

    expr_ref pr2(m), fml2(m);
    expr_ref_vector bound(m);
    ptr_vector<sort> sorts;
    svector<symbol> names;
    for (unsigned i = 0; i < vars.size(); ++i) {
        bound.push_back(vars[i].get());
        names.push_back(vars[i]->get_decl()->get_name());
        sorts.push_back(m.get_sort(vars[i].get()));
    }
    expr_abstract(m, 0, bound.size(), bound.c_ptr(), fml, fml2);
    fml2 = m.mk_exists(bound.size(), sorts.c_ptr(), names.c_ptr(), fml2);
    qe::expr_quant_elim qe(m, params);
    expr_ref pr1 = qe::arith_project(*md, vars, lits);
    qe(m.mk_true(), fml2, pr2);
    std::cout << mk_pp(pr1, m) << "\n";
    std::cout << mk_pp(pr2, m) << "\n";

    expr_ref npr2(m);
    npr2 = m.mk_not(pr2);
    ctx.push();
    ctx.assert_expr(pr1);
    ctx.assert_expr(npr2);
    VERIFY(l_false == ctx.check());
    ctx.pop(1);
    
    
}

void tst_qe_arith() {
    test2(example6);
    return;
    test(example1);
    test(example2);
    test(example3);
    test(example4);
    test(example5);
}
