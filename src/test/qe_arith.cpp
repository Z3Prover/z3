
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
#include "smt_context.h"
#include "expr_abstract.h"
#include "expr_safe_replace.h"

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
           << "(declare-const i Int)\n"
           << "(declare-const j Int)\n"
           << "(declare-const k Int)\n"
           << "(declare-const l Int)\n"
           << "(declare-const m Int)\n"
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
static char const* example7 = "(and (<= x y) (<= x z) (<= u x) (< v x))";
static char const* example8 = "(and  (<= (* 2 i) k) (<= j (* 3 i)))";

static char const* example6 = "(and (<= 0 (+ x z))\
     (>= y x) \
     (<= y x)\
     (<= (- u y) 0.0)\
     (>= x (+ v z))\
     (>= x 0.0)\
     (<= x 1.0))";

// phi[M] => result => E x . phi[x] 

static void test(app* var, expr_ref& fml) {

    ast_manager& m = fml.get_manager();
    smt_params params;
    params.m_model = true;

    symbol x_name(var->get_decl()->get_name());   
    sort* x_sort = m.get_sort(var);

    expr_ref pr(m);
    expr_ref_vector lits(m);
    flatten_and(fml, lits);

    model_ref md;
    {
        smt::context ctx(m, params);
        ctx.assert_expr(fml);
        lbool result = ctx.check();
        if (result != l_true) return;
        ctx.get_model(md);
    }    
    VERIFY(qe::arith_project(*md, var, lits));
    pr = mk_and(lits);
   
    std::cout << "original:  " << mk_pp(fml, m) << "\n";
    std::cout << "projected: " << mk_pp(pr,  m) << "\n";

    // projection is consistent with model.
    expr_ref tmp(m);
    VERIFY(md->eval(pr, tmp) && m.is_true(tmp));       

    // projection implies E x. fml
    {
        qe::expr_quant_elim qelim(m, params);
        expr_ref result(m), efml(m);
        expr* x = var;
        expr_abstract(m, 0, 1, &x, fml, efml);
        efml = m.mk_exists(1, &x_sort, &x_name, efml);
        qelim(m.mk_true(), efml, result);

        smt::context ctx(m, params);
        ctx.assert_expr(pr);
        ctx.assert_expr(m.mk_not(result));
        std::cout << "exists: " << pr << " =>\n" << result << "\n";
        VERIFY(l_false == ctx.check());
    }    

    std::cout << "\n";
}



static void testR(char const *ex) {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    symbol x_name("x");
    sort_ref x_sort(a.mk_real(), m);
    app_ref var(m.mk_const(x_name, x_sort), m);
    test(var, fml);
}

static void testI(char const *ex) {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref fml = parse_fml(m, ex);
    symbol x_name("i");
    sort_ref x_sort(a.mk_int(), m);
    app_ref var(m.mk_const(x_name, x_sort), m);
    test(var, fml);
}

static expr_ref_vector mk_ineqs(app* x, app* y, app_ref_vector const& nums) {
    ast_manager& m = nums.get_manager();
    arith_util a(m);
    expr_ref_vector result(m);
    for (unsigned i = 0; i < nums.size(); ++i) {
        expr_ref ax(a.mk_mul(nums[i], x), m);
        result.push_back(a.mk_le(ax, y));
        result.push_back(m.mk_not(a.mk_ge(ax, y)));
        result.push_back(m.mk_not(a.mk_gt(y, ax)));
        result.push_back(a.mk_lt(y, ax));
    }
    return result;
}

static app_ref generate_ineqs(ast_manager& m, sort* s, vector<expr_ref_vector>& cs, bool mods_too) {
    arith_util a(m);
    app_ref_vector vars(m), nums(m);
    vars.push_back(m.mk_const(symbol("x"), s));
    vars.push_back(m.mk_const(symbol("y"), s));
    vars.push_back(m.mk_const(symbol("z"), s));
    vars.push_back(m.mk_const(symbol("u"), s));
    vars.push_back(m.mk_const(symbol("v"), s));
    vars.push_back(m.mk_const(symbol("w"), s));
    nums.push_back(a.mk_numeral(rational(1),  s));
    nums.push_back(a.mk_numeral(rational(2),  s));
    nums.push_back(a.mk_numeral(rational(3),  s));
    
    app* x = vars[0].get();
    app* y = vars[1].get();
    app* z = vars[2].get();
    // 
    // ax <= by, ax < by, not (ax >= by), not (ax > by)
    // 
    cs.push_back(mk_ineqs(x, vars[1].get(), nums));
    cs.push_back(mk_ineqs(x, vars[2].get(), nums));
    cs.push_back(mk_ineqs(x, vars[3].get(), nums));
    cs.push_back(mk_ineqs(x, vars[4].get(), nums));
    cs.push_back(mk_ineqs(x, vars[5].get(), nums));

    if (mods_too) {
        expr_ref_vector mods(m);
        expr_ref zero(a.mk_numeral(rational(0), s), m);
        mods.push_back(m.mk_true());
        for (unsigned j = 0; j < nums.size(); ++j) {
            mods.push_back(m.mk_eq(a.mk_mod(a.mk_add(a.mk_mul(nums[j].get(),x), y), nums[1].get()), zero));
        }
        cs.push_back(mods);
        mods.resize(1);
        for (unsigned j = 0; j < nums.size(); ++j) {
            mods.push_back(m.mk_eq(a.mk_mod(a.mk_add(a.mk_mul(nums[j].get(),x), y), nums[2].get()), zero));
        }
        cs.push_back(mods);
    }
    return app_ref(x, m);
}


static void test_c(app* x, expr_ref_vector const& c) {
    ast_manager& m = c.get_manager();
    expr_ref fml(m);
    fml = m.mk_and(c.size(), c.c_ptr());
    test(x, fml);
}

static void test_cs(app* x, expr_ref_vector& c, vector<expr_ref_vector> const& cs) {
    if (c.size() == cs.size()) {
        test_c(x, c);
        return;
    }
    expr_ref_vector const& c1 = cs[c.size()];
    for (unsigned i = 0; i < c1.size(); ++i) {
        c.push_back(c1[i]);
        test_cs(x, c, cs);
        c.pop_back();
    }
}


static void test_ineqs(ast_manager& m, sort* s, bool mods_too) {
    vector<expr_ref_vector> ineqs;
    app_ref x = generate_ineqs(m, s, ineqs, mods_too);
    expr_ref_vector cs(m);
    test_cs(x, cs, ineqs);
}

static void test_ineqs() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    sort* s_int = a.mk_int();
    sort* s_real = a.mk_real();
    test_ineqs(m, s_int, true);
    test_ineqs(m, s_real, false);
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

    expr_ref pr1(m), pr2(m), fml2(m);
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
    for (unsigned i = 0; i < vars.size(); ++i) {
        VERIFY(qe::arith_project(*md, vars[i].get(), lits));
    }
    pr1 = mk_and(lits);
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
//    enable_trace("qe");
    testI(example8);    
    testR(example7);
    test_ineqs();
    return;
    testR(example1);
    testR(example2);
    testR(example3);
    testR(example4);
    testR(example5);
    return;
    test2(example6);
    return;
}
