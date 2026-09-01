
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/smt_context.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "solver/solver.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/fpa/fpa2bv_tactic.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/smtlogics/smt_tactic.h"
#include <sstream>

void tst_smt_context()
{
    smt_params params;

    ast_manager m;
    reg_decl_plugins(m);

    smt::context ctx(m, params);

    app_ref a1(m.mk_const(symbol("a"), m.mk_bool_sort()), m);
    app_ref b1(m.mk_const(symbol("b"), m.mk_bool_sort()), m);
    app_ref c1(m.mk_const(symbol("c"), m.mk_bool_sort()), m);
    app_ref na1(m.mk_not(a1), m);
    ctx.assert_expr(na1);

    app_ref b_or_c(m.mk_or(c1.get(), b1.get()), m);
    ctx.assert_expr(b_or_c);

    {
        app_ref nc(m.mk_not(c1), m);
        ptr_vector<expr> assumptions;
        assumptions.push_back(nc.get());

        ctx.check(assumptions.size(), assumptions.data());
    }

    ctx.check();

    {
        arith_util a(m);
        expr_ref x(m.mk_var(2, a.mk_int()), m);
        expr_ref x4(m.mk_var(1, a.mk_int()), m);
        expr_ref y(m.mk_var(0, a.mk_int()), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref two(a.mk_int(2), m);
        expr_ref_vector conjs(m);
        conjs.push_back(a.mk_gt(x, y));
        conjs.push_back(a.mk_gt(zero, x4));
        conjs.push_back(a.mk_gt(zero, a.mk_uminus(y)));
        conjs.push_back(a.mk_lt(zero, a.mk_uminus(a.mk_mul(two, y))));
        expr_ref body(m.mk_and(conjs), m);

        sort* y_sort = a.mk_int();
        symbol y_name("y");
        body = m.mk_exists(1, &y_sort, &y_name, body);

        sort* sorts[2] = { a.mk_int(), a.mk_int() };
        symbol names[2] = { symbol("x"), symbol("x4") };
        expr_ref q(m.mk_forall(2, sorts, names, body), m);

        smt::context qctx(m, params);
        qctx.assert_expr(q);
        VERIFY(l_false == qctx.check());
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Node 0)) (((base) (wrapped (payload Float32)))))\n"
            "(define-fun measure ((node Node) (fallback Int)) Int\n"
            "  (ite ((_ is wrapped) node) 1 fallback))\n"
            "(assert\n"
            "  (forall ((other Node))\n"
            "    (= (measure base 0)\n"
            "       (measure other 0))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        smt::context qctx(m, params);
        for (expr* a : cmd.assertions())
            qctx.assert_expr(a);
        VERIFY(l_false == qctx.check());
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-sort Element)\n"
            "(declare-sort Index)\n"
            "(declare-fun e6 () Element)\n"
            "(declare-fun i6 () Index)\n"
            "(declare-fun i2 () Index)\n"
            "(declare-fun i4 () Index)\n"
            "(declare-fun e9 () Element)\n"
            "(declare-fun i8 () Index)\n"
            "(declare-fun i10 () Index)\n"
            "(declare-fun a1 () (Array Index Element))\n"
            "(assert (exists ((i3 Index)) (and (= i3 i8) (= i6 i10) "
            "(not (= (store (store (store a1 i4 e9) i2 e6) i10 e6) "
            "(store (store (store a1 i6 e9) i8 e6) i10 e9))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("rewriter.expand_nested_stores", true);
        tactic_ref t = mk_lira_tactic(m, p);
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        VERIFY(l_true == check_sat(*t, g, md, labels, pr, core, reason_unknown));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(declare-const y (_ BitVec 1))\n"
            "(assert\n"
            "  (exists ((V (_ BitVec 8)))\n"
            "    (= (_ bv1 8)\n"
            "       ((_ extract 7 0)\n"
            "         (bvlshr\n"
            "           (concat V (_ bv0 8))\n"
            "           ((_ zero_extend 15) y))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", true);
        p.set_uint("bv.solver", 2);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_false == slv->check_sat(0, nullptr));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(assert\n"
            "  (exists ((V (_ BitVec 1)))\n"
            "    (= (_ bv0 1) (bvashr (_ bv1 1) V))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", true);
        p.set_uint("bv.solver", 2);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_false == slv->check_sat(0, nullptr));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-const x (_ FloatingPoint 5 11))\n"
            "(declare-const y (_ FloatingPoint 5 11))\n"
            "(declare-const xb (_ BitVec 16))\n"
            "(declare-const yb (_ BitVec 16))\n"
            "(assert (= x ((_ to_fp 5 11) xb)))\n"
            "(assert (= y ((_ to_fp 5 11) yb)))\n"
            "(assert (= xb #b1000001111000111))\n"
            "(assert (= yb #b0011110111000000))\n"
            "(assert (not (= ((_ fp.to_ieee_bv 16) (fp.fma RNE x y x)) #x889b)))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        tactic_ref t = and_then(mk_fpa2bv_tactic(m), mk_simplify_tactic(m), mk_bit_blaster_tactic(m), mk_smt_tactic(m));
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        VERIFY(l_false == check_sat(*t, g, md, labels, pr, core, reason_unknown));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-fun length ((Array Int Int)) Int)\n"
            "(declare-const lindx2 (Array Int Int))\n"
            "(declare-const indx1 (Array Int Int))\n"
            "(declare-const orig_findx1 (Array Int Int))\n"
            "(assert (and\n"
            "  (forall ((i Int) (j Int))\n"
            "    (let ((a!1 (and (<= 0 i)\n"
            "                    (<= i (- (length indx1) 1))\n"
            "                    (<= 0 j)\n"
            "                    (<= j (- (length orig_findx1) 1))\n"
            "                    (= i j))))\n"
            "      (=> a!1 (= (select indx1 i) (select orig_findx1 j)))))\n"
            "  (= (length lindx2) 11)\n"
            "  (forall ((i Int)) (=> (and (<= 3 i) (<= i 25)) (= (select indx1 i) (- 1))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_true == slv->check_sat(0, nullptr));
    }
}
