/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    psmt.cpp

Abstract:

    Tests for the parallel SMT tactic (psmt).
    Regression test for GitHub issue #9985 (deadlock on psmt).

--*/
#ifndef SINGLE_THREAD

#include "ast/reg_decl_plugins.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "smt/smt_solver.h"
#include "smt/tactic/smt_tactic_core.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include <iostream>

// Regression test for GitHub issue #9985:
//
// psmt used to deadlock when every CDCL worker returned l_undef with a
// reason other than "max-conflicts-reached" (e.g., theory incompleteness).
// batch_manager::set_unknown() changed the terminal state but did not
// notify backbone workers or the core-minimizer worker that were blocked on
// their condition variables.  Those workers blocked forever.
//
// Fix: set_unknown() now calls m_bb_cv.notify_all() and
// m_core_min_cv.notify_all() so all waiting helper threads observe the
// state change and exit cleanly.
//
// We exercise three cases:
//   1. SAT  – trivially satisfiable boolean formula.
//   2. UNSAT – trivially unsatisfiable boolean formula.
//   3. UNKNOWN (no deadlock) – formula whose root cube is theory-incomplete.
//      The formula uses (as-array f) terms for a function f : Int -> Bool.
//      The array theory marks itself incomplete for as-array, so every
//      CDCL worker returns l_undef with "(incomplete (theory array))",
//      triggering the set_unknown path that used to deadlock.
static void tst_psmt_worker() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;

    // ------------------------------------------------------------------
    // 1. SAT test: assert (or x (not x)) – always true
    // ------------------------------------------------------------------
    {
        tactic_ref t = mk_parallel_smt_tactic(m, p);
        goal_ref   g = alloc(goal, m, false, true, false);
        expr_ref   x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
        g->assert_expr(m.mk_or(x, m.mk_not(x)));

        model_ref           md;
        labels_vec          labels;
        proof_ref           pr(m);
        expr_dependency_ref core(m);
        std::string         reason_unknown;
        lbool r = check_sat(*t, g, md, labels, pr, core, reason_unknown);
        SASSERT(r == l_true);
        (void)r;
        std::cout << "psmt SAT: " << r << "\n";
    }

    // ------------------------------------------------------------------
    // 2. UNSAT test: assert (and x (not x))
    // ------------------------------------------------------------------
    {
        tactic_ref t = mk_parallel_smt_tactic(m, p);
        goal_ref   g = alloc(goal, m, false, true, false);
        expr_ref   x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
        g->assert_expr(m.mk_and(x, m.mk_not(x)));

        model_ref           md;
        labels_vec          labels;
        proof_ref           pr(m);
        expr_dependency_ref core(m);
        std::string         reason_unknown;
        lbool r = check_sat(*t, g, md, labels, pr, core, reason_unknown);
        SASSERT(r == l_false);
        (void)r;
        std::cout << "psmt UNSAT: " << r << "\n";
    }

    // ------------------------------------------------------------------
    // 3. UNKNOWN (deadlock regression) test.
    //
    // Reproduce: (declare-fun f (Int) Bool)
    //            (declare-fun g (Int) Bool)
    //            (assert (distinct f g))
    //            (check-sat-using psmt)
    //
    // In SMT-LIB2, the function symbols f and g are lifted to array terms
    // via (as-array f) and (as-array g).  The array theory is explicitly
    // incomplete for as-array, so check_sat returns l_undef with reason
    // "(incomplete (theory array))".  Previously set_unknown() forgot to
    // notify backbone and core-minimizer workers' condition variables,
    // causing a deadlock; now it does.
    // ------------------------------------------------------------------
    {
        tactic_ref t = mk_parallel_smt_tactic(m, p);
        goal_ref   g = alloc(goal, m, false, true, false);

        // Build func_decls: f : Int -> Bool, g : Int -> Bool
        arith_util arith(m);
        sort* int_s     = arith.mk_int();
        sort* domain[1] = { int_s };
        func_decl* f_decl = m.mk_func_decl(symbol("f_fn"), 1, domain, m.mk_bool_sort());
        func_decl* g_decl = m.mk_func_decl(symbol("g_fn"), 1, domain, m.mk_bool_sort());

        // (as-array f) and (as-array g): array representations of f and g
        array_util autil(m);
        expr_ref f_arr(autil.mk_as_array(f_decl), m);
        expr_ref g_arr(autil.mk_as_array(g_decl), m);

        // (distinct (as-array f) (as-array g))
        expr* dist_args[2] = { f_arr, g_arr };
        expr_ref distinct_fg(m.mk_distinct(2, dist_args), m);
        g->assert_expr(distinct_fg);

        model_ref           md;
        labels_vec          labels;
        proof_ref           pr(m);
        expr_dependency_ref core(m);
        std::string         reason_unknown;
        lbool r = check_sat(*t, g, md, labels, pr, core, reason_unknown);
        // The result must be l_undef (theory-incomplete).
        // If the fix is absent, this call deadlocks instead of returning.
        SASSERT(r == l_undef);
        (void)r;
        std::cout << "psmt UNKNOWN (no deadlock): " << r << "\n";
    }

    std::cout << "psmt tests passed\n";
}

void tst_psmt() {
    tst_psmt_worker();
}

#else

void tst_psmt() {
    // Single-threaded build: parallel tactic degrades to sequential.
    // No deadlock is possible; nothing to test.
}

#endif
