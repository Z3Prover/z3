/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_basic.cpp

Abstract:

    Basic unit tests for theory_nseq and supporting infrastructure.

--*/
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "params/smt_params.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"
#include "smt/theory_nseq.h"
#include <iostream>

// Trivial solver that always returns sat and ignores all assertions.
class nseq_basic_dummy_solver : public seq::sub_solver_i {
public:
    void push() override {}
    void pop(unsigned) override {}
    void assert_expr(expr* e, seq::dep_tracker dep) override {}

    void reset() override {}
    lbool check() override { return l_true; }
};

// Test 1: instantiation of nielsen_graph compiles and doesn't crash
static void test_nseq_instantiation() {
    std::cout << "test_nseq_instantiation\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    const seq::nielsen_graph ng(sg, solver, context_solver);
    SASSERT(ng.root() == nullptr);
    SASSERT(ng.num_nodes() == 0);
    std::cout << "  ok\n";
}

// Test 2: parameter validation accepts "nseq"
static void test_nseq_param_validation() {
    std::cout << "test_nseq_param_validation\n";
    const smt_params p;
    // Should not throw
    try {
        p.validate_string_solver(symbol("nseq"));
        std::cout << "  ok: nseq accepted\n";
    } catch (...) {
        SASSERT(false && "nseq should be accepted as a valid string_solver value");
    }
    // Should not throw for legacy values
    try {
        p.validate_string_solver(symbol("seq"));
        p.validate_string_solver(symbol("auto"));
        p.validate_string_solver(symbol("none"));
        std::cout << "  ok: legacy values still accepted\n";
    } catch (...) {
        SASSERT(false && "legacy values should still be accepted");
    }
}

// Test 2b: parameter validation rejects invalid variants of "nseq"
static void test_nseq_param_validation_rejects_invalid() {
    std::cout << "test_nseq_param_validation_rejects_invalid\n";
    const smt_params p;
    static const char* invalid_variants[] = { "nseq3", "NSEQ", "nseqq", "nse", "Nseq", "nseq ", "" };
    for (const auto s : invalid_variants) {
        bool threw = false;
        try {
            p.validate_string_solver(symbol(s));
        } catch (...) {
            threw = true;
        }
        if (!threw) {
            std::cerr << "  FAIL: '" << s << "' should have been rejected\n";
            SASSERT(false && "invalid string solver variant was accepted");
        }
    }
    std::cout << "  ok: all invalid variants rejected\n";
}

// Test 3: nielsen graph simplification (trivial case)
static void test_nseq_simplification() {
    std::cout << "test_nseq_simplification\n";
    ast_manager m;
    reg_decl_plugins(m);
    const seq_util su(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    // Add a trivial equality: empty = empty
    euf::snode const* empty1 = sg.mk_empty_seq(su.str.mk_string_sort());
    euf::snode const* empty2 = sg.mk_empty_seq(su.str.mk_string_sort());

    ng.add_str_eq(empty1, empty2);

    const seq::nielsen_graph::search_result r = ng.solve();
    // empty = empty is trivially satisfied
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: trivial equality solved as sat\n";
}

// Test 4: node is_satisfied check
static void test_nseq_node_satisfied() {
    std::cout << "test_nseq_node_satisfied\n";
    ast_manager m;
    reg_decl_plugins(m);
    const seq_util su(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    seq::nielsen_node *node = ng.mk_node();
    // empty node has no constraints => satisfied
    SASSERT(node->is_satisfied());

    // a trivial equality is dropped already at insertion (add_str_eq)
    const euf::snode *empty = sg.mk_empty_seq(su.str.mk_string_sort());
    const seq::dep_tracker dep = nullptr;
    const seq::str_eq eq(m, empty, empty, dep);
    node->add_str_eq(eq);
    SASSERT(node->str_eqs().empty());
    SASSERT(node->is_satisfied());
    const ptr_vector<seq::nielsen_edge> cur_path;
    const seq::simplify_result sr = node->simplify_and_init(cur_path);

    VERIFY(sr == seq::simplify_result::satisfied || sr == seq::simplify_result::proceed);
    std::cout << "  ok\n";
}

// Test 5: symbol clash conflict ("a" = "b" is unsat)
static void test_nseq_symbol_clash() {
    std::cout << "test_nseq_symbol_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* a = sg.mk_char('a');
    euf::snode const* b = sg.mk_char('b');
    ng.add_str_eq(a, b);

    const auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);

    // verify conflict explanation returns the equality index
    smt::enode_pair_vector eqs;
    sat::literal_vector mem_idx;
    ng.test_aux_explain_conflict(eqs, mem_idx);
    SASSERT(eqs.size() == 1);
    SASSERT(eqs[0].first == nullptr);
    SASSERT(mem_idx.empty());
    std::cout << "  ok: symbol clash detected as unsat\n";
}

// Test 6: variable equality x = x is sat
static void test_nseq_var_eq_self() {
    std::cout << "test_nseq_var_eq_self\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    ng.add_str_eq(x, x);

    const auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: x = x solved as sat\n";
}

// Test 7: x·a = x·b is unsat (prefix match then clash)
static void test_nseq_prefix_clash() {
    std::cout << "test_nseq_prefix_clash\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* b = sg.mk_char('b');
    euf::snode const* xa = sg.mk_concat(x, a);
    euf::snode const* xb = sg.mk_concat(x, b);

    ng.add_str_eq(xa, xb);
    const auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);
    std::cout << "  ok: x·a = x·b detected as unsat\n";
}

// Test 8: a·x = a·y has solutions (not unsat)
static void test_nseq_const_nielsen_solvable() {
    std::cout << "test_nseq_const_nielsen_solvable\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);

    euf::snode const* x = sg.mk_var(symbol("x"), sg.get_str_sort());
    euf::snode const* y = sg.mk_var(symbol("y"), sg.get_str_sort());
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* ax = sg.mk_concat(a, x);
    euf::snode const* ay = sg.mk_concat(a, y);

    ng.add_str_eq(ax, ay);
    const auto r = ng.solve();
    // a·x = a·y simplifies to x = y which is satisfiable (x = y = ε)
    SASSERT(r == seq::nielsen_graph::search_result::sat);
    std::cout << "  ok: a·x = a·y solved as sat\n";
}

// Test 9: length mismatch - "ab" = "a" is unsat
static void test_nseq_length_mismatch() {
    std::cout << "test_nseq_length_mismatch\n";
    ast_manager m;
    reg_decl_plugins(m);
    euf::egraph eg(m);
    euf::sgraph sg(m, eg);
    nseq_basic_dummy_solver solver;
    seq::context_solver_i context_solver;
    seq::nielsen_graph ng(sg, solver, context_solver);
    euf::snode const* a = sg.mk_char('a');
    euf::snode const* b = sg.mk_char('b');
    euf::snode const* ab = sg.mk_concat(a, b);

    ng.add_str_eq(ab, a);
    const auto r = ng.solve();
    SASSERT(r == seq::nielsen_graph::search_result::unsat);
    std::cout << "  ok: ab = a detected as unsat\n";
}

// Test 10: setup_seq_str dispatches to setup_nseq() when string_solver == "nseq"
static void test_setup_seq_str_dispatches_nseq() {
    std::cout << "test_setup_seq_str_dispatches_nseq\n";
    ast_manager m;
    reg_decl_plugins(m);

    smt_params params;
    params.m_string_solver = symbol("nseq");

    smt::context ctx(m, params);

    // Assert a string equality to trigger string theory setup during check()
    const seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    const app_ref x(m.mk_const(symbol("x_setup_test"), str_sort), m);
    const app_ref eq(m.mk_eq(x.get(), x.get()), m);
    ctx.assert_expr(eq);
    ctx.check();

    // Verify that theory_nseq (not theory_seq) was registered for the "seq" family
    const family_id seq_fid = m.mk_family_id("seq");
    SASSERT(ctx.get_theory(seq_fid) != nullptr);
    SASSERT(dynamic_cast<smt::theory_nseq*>(ctx.get_theory(seq_fid)) != nullptr);
    std::cout << "  ok: setup_seq_str dispatched to setup_nseq for 'nseq'\n";
}

// -----------------------------------------------------------------------
// Fine & Wilf end-to-end tests (full smt::context, real arithmetic).
// The equation shape U^n·V = Y·W^m·Z with different-base powers used to
// diverge under the const-num-unwinding peel; apply_fine_wilf (priority 3c,
// smt.nseq.fine_wilf) closes it.  See specs/nseq-fine-wilf.md.
// -----------------------------------------------------------------------

// Shared builder: asserts  "a"·(ba)^n·mid_l·u  ==  (ab)^n·"a"·mid_r·v ∧ n ≥ 0
// into ctx.  mid_l/mid_r are ground infixes ("" = none).
static void assert_fine_wilf_eq(smt::context& ctx, ast_manager& m,
                                const char* mid_l, const char* mid_r) {
    seq_util su(m);
    arith_util au(m);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref u(m.mk_const(symbol("u"), str_sort), m);
    const expr_ref v(m.mk_const(symbol("v"), str_sort), m);
    const expr_ref pow_ba(su.str.mk_power(su.str.mk_string(zstring("ba")), n), m);
    const expr_ref pow_ab(su.str.mk_power(su.str.mk_string(zstring("ab")), n), m);

    expr_ref lhs(su.str.mk_concat(su.str.mk_string(zstring("a")), pow_ba), m);
    if (*mid_l)
        lhs = su.str.mk_concat(lhs, su.str.mk_string(zstring(mid_l)));
    lhs = su.str.mk_concat(lhs, u);

    expr_ref rhs(su.str.mk_concat(pow_ab, su.str.mk_string(zstring("a"))), m);
    if (*mid_r)
        rhs = su.str.mk_concat(rhs, su.str.mk_string(zstring(mid_r)));
    rhs = su.str.mk_concat(rhs, v);

    ctx.assert_expr(expr_ref(au.mk_ge(n, au.mk_int(0)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
}

// UNSAT: "a"·(ba)^n·"ab"·u == (ab)^n·"a"·"ba"·v has no solution (after
// aligning the periodic parts the remainders force "ab"·u = "ba"·v with
// equal-position clash for every n).  Diverges with fine_wilf disabled —
// this is the regression test for the peel loop.
static void test_nseq_fine_wilf_e2e_unsat() {
    std::cout << "test_nseq_fine_wilf_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    SASSERT(!params.m_nseq_fine_wilf); // opt-in feature: default off
    params.m_nseq_fine_wilf = true;
    smt::context ctx(m, params);
    assert_fine_wilf_eq(ctx, m, "ab", "ba");
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// SAT: the draft's test 1, "a"·(ba)^n·u == (ab)^n·"a"·v — u = v solves it
// for every n (a·(ba)^n = (ab)^n·a is the conjugation identity).
static void test_nseq_fine_wilf_e2e_sat() {
    std::cout << "test_nseq_fine_wilf_e2e_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_fine_wilf = true; // opt-in (default off)
    smt::context ctx(m, params);
    assert_fine_wilf_eq(ctx, m, "", "");
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// Option off (the default): the SAT instance is still solved (the n = 0
// peel branch closes it without Fine & Wilf), exercising the default
// smt.nseq.fine_wilf=false path end-to-end.  (The UNSAT instance would
// diverge here — by design.)
static void test_nseq_fine_wilf_option_off() {
    std::cout << "test_nseq_fine_wilf_option_off\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_fine_wilf = false; // explicit for clarity (= the default)
    smt::context ctx(m, params);
    assert_fine_wilf_eq(ctx, m, "", "");
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat with fine_wilf disabled\n";
}

// -----------------------------------------------------------------------
// Nested-power cursor end-to-end tests (full smt::context, real arithmetic).
// A power whose base itself contains a ground power, e.g. (a·(bc)^p·d)^n.
// The outer one-copy peel diverges here; apply_power_cursor (unified) (priority
// 3e) re-bases both outer powers over their common token-level root.
// See specs/nseq-power-cursor.md §4b.
// -----------------------------------------------------------------------

// Builds, into ctx:  "a"·((bc)^p·"a")^n·trail_l  ==  (a·(bc)^p)^n·trail_r
// with the SAME outer exponent n (≥ 0) and p (≥ p_lo).  trail_l/trail_r are
// ground expr suffixes (nullptr = none).
static void assert_nested_conjugate_eq(smt::context& ctx, ast_manager& m,
                                       unsigned p_lo, expr* trail_l, expr* trail_r) {
    seq_util su(m);
    arith_util au(m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref A(su.str.mk_string(zstring("a")), m);
    const expr_ref bcp(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m);
    const expr_ref base1(su.str.mk_concat(bcp, A), m);            // (bc)^p·a
    const expr_ref base2(su.str.mk_concat(A, bcp), m);            // a·(bc)^p
    const expr_ref pow1(su.str.mk_power(base1, n), m);
    const expr_ref pow2(su.str.mk_power(base2, n), m);

    expr_ref lhs(su.str.mk_concat(A, pow1), m);                   // a·((bc)^p a)^n
    if (trail_l) lhs = su.str.mk_concat(lhs, expr_ref(trail_l, m));
    expr_ref rhs(pow2, m);                                        // (a (bc)^p)^n
    if (trail_r) rhs = su.str.mk_concat(rhs, expr_ref(trail_r, m));

    ctx.assert_expr(expr_ref(au.mk_ge(n, au.mk_int(0)), m));
    ctx.assert_expr(expr_ref(au.mk_ge(p, au.mk_int((int)p_lo)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
}

// UNSAT: a·((bc)^p·a)^n·"a"·(bc)^p·u == (a·(bc)^p)^n·"a"·(bc)^p·"a"·v with p ≥ 1
// (the nested analog of the ex1 conjugate clash — after the token-level re-base
// and cancellation it forces "a"·(bc)^p·u == (bc)^p·"a"·v, an equal-position
// 'a' vs 'b' clash for every n,p≥1).  DIVERGES on the outer peel without
// apply_power_cursor (unified); a node budget guards a regressed build against a
// hang (it would then return unknown ≠ l_false and fail cleanly).
static void test_nseq_power_cursor_nested_e2e_unsat() {
    std::cout << "test_nseq_power_cursor_nested_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 100000; // closes in ~7 nodes with the feature
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref bcp(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m);
    const expr_ref u(m.mk_const(symbol("u"), su.str.mk_string_sort()), m);
    const expr_ref v(m.mk_const(symbol("v"), su.str.mk_string_sort()), m);
    const expr_ref tl(su.str.mk_concat(su.str.mk_string(zstring("a")),
                                       su.str.mk_concat(bcp, u)), m);       // "a"·(bc)^p·u
    const expr_ref tr(su.str.mk_concat(su.str.mk_string(zstring("a")),
                          su.str.mk_concat(bcp,
                              su.str.mk_concat(su.str.mk_string(zstring("a")), v))), m); // "a"·(bc)^p·"a"·v
    assert_nested_conjugate_eq(ctx, m, /*p_lo*/1, tl, tr);
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// SAT: a·((bc)^p·a)^n == (a·(bc)^p)^n·"a" is the conjugation identity
// a·((bc)^p a)^n = (a (bc)^p)^n·a, true for every n,p — the nested analog of
// the fine_wilf SAT identity.  Exercises the re-base to a satisfiable leaf.
static void test_nseq_power_cursor_nested_e2e_sat() {
    std::cout << "test_nseq_power_cursor_nested_e2e_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 100000;
    smt::context ctx(m, params);
    seq_util su(m);
    assert_nested_conjugate_eq(ctx, m, /*p_lo*/0, nullptr,
                               su.str.mk_string(zstring("a")));  // trail_r = "a"
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// Nested power-of-power ((bc)^p)^n = ((bcbc)^q)^m with p,q,n,m ≥ 1.
// apply_power_normalize flattens (z^a)^b → z^{a·b} and normalises "bcbc" → "bc",
// after which the cursor re-bases to (bc)^{p·n} = (bc)^{2·q·m} and num_cmp emits
// the NONLINEAR constraint p·n = 2·q·m (satisfiable, e.g. p=2,n=q=m=1).  The
// bare outer-copy peel diverges here; a node budget guards a regression.
static void test_nseq_power_normalize_e2e_sat() {
    std::cout << "test_nseq_power_normalize_e2e_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 100000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref bc_p(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m);
    const expr_ref bcbc_q(su.str.mk_power(su.str.mk_string(zstring("bcbc")), q), m);
    const expr_ref lhs(su.str.mk_power(bc_p, n), m);      // ((bc)^p)^n
    const expr_ref rhs(su.str.mk_power(bcbc_q, mm), m);   // ((bcbc)^q)^m
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// SAT: (a·(bc)^p)^n = (a·(bc)^{2q})^m with p,q,n,m ≥ 1.  The nested conjugate
// residual the char cursor declines: apply_power_commute reduces it to the word
// equation (a(bc)^p)(a(bc)^{2q}) = (a(bc)^{2q})(a(bc)^p) plus n(1+2p) = m(1+4q),
// solved to p = 2q ∧ n = m (e.g. q=1,p=2,n=m=1).  Diverges without the rule.
static void test_nseq_power_commute_e2e_sat() {
    std::cout << "test_nseq_power_commute_e2e_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 100000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref bc_p(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m);
    const expr_ref bc_2q(su.str.mk_power(su.str.mk_string(zstring("bc")),
                                         expr_ref(au.mk_mul(au.mk_int(2), q), m)), m);
    const expr_ref U(su.str.mk_concat(su.str.mk_string(zstring("a")), bc_p), m);   // a·(bc)^p
    const expr_ref V(su.str.mk_concat(su.str.mk_string(zstring("a")), bc_2q), m);  // a·(bc)^{2q}
    const expr_ref lhs(su.str.mk_power(U, n), m);
    const expr_ref rhs(su.str.mk_power(V, mm), m);
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// UNSAT: the same equation with the extra constraint p = 2q + 1 — the 'a'
// positions can no longer align (p = 2q is forced by commutation), so it is
// unsatisfiable.  Diverges without apply_power_commute.
static void test_nseq_power_commute_e2e_unsat() {
    std::cout << "test_nseq_power_commute_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 100000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref bc_p(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m);
    const expr_ref bc_2q(su.str.mk_power(su.str.mk_string(zstring("bc")),
                                         expr_ref(au.mk_mul(au.mk_int(2), q), m)), m);
    const expr_ref U(su.str.mk_concat(su.str.mk_string(zstring("a")), bc_p), m);
    const expr_ref V(su.str.mk_concat(su.str.mk_string(zstring("a")), bc_2q), m);
    const expr_ref lhs(su.str.mk_power(U, n), m);
    const expr_ref rhs(su.str.mk_power(V, mm), m);
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(p, au.mk_add(au.mk_mul(au.mk_int(2), q), au.mk_int(1))), m)); // p = 2q+1
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// Fully-ground TAILED power head (apply_ground_power_split, priority 3e2).
// (a·(bc)^p)^n · "d" = (a·(bc)^{2q})^m · "d" — the R1 residual with a ground tail,
// which apply_power_commute (pure only) skips.  Equal tails force the equal-length
// race branch → P^e=Q^f (commute) → p=2q, n=m.  SAT.
static void test_nseq_gpsplit_e2e_sat() {
    std::cout << "test_nseq_gpsplit_e2e_sat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 300000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref U(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m)), m);
    const expr_ref V(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")),
                              expr_ref(au.mk_mul(au.mk_int(2), q), m)), m)), m);
    const expr_ref lhs(su.str.mk_concat(expr_ref(su.str.mk_power(U, n), m), su.str.mk_string(zstring("d"))), m);
    const expr_ref rhs(su.str.mk_concat(expr_ref(su.str.mk_power(V, mm), m), su.str.mk_string(zstring("d"))), m);
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// Same, with p = 2q+1 forced → the 'a' positions cannot align → UNSAT.
static void test_nseq_gpsplit_e2e_unsat() {
    std::cout << "test_nseq_gpsplit_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 300000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref U(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m)), m);
    const expr_ref V(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")),
                              expr_ref(au.mk_mul(au.mk_int(2), q), m)), m)), m);
    const expr_ref lhs(su.str.mk_concat(expr_ref(su.str.mk_power(U, n), m), su.str.mk_string(zstring("d"))), m);
    const expr_ref rhs(su.str.mk_concat(expr_ref(su.str.mk_power(V, mm), m), su.str.mk_string(zstring("d"))), m);
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(p, au.mk_add(au.mk_mul(au.mk_int(2), q), au.mk_int(1))), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// Commutation of two DIFFERENT nested powers as a fully-ground word equation:
// X·Y = Y·X with X=(a(bc)^p)^n, Y=(a(bc)^{2q})^m.  Exercises the split with
// nonempty tails on BOTH sides; satisfiable (p=2q ⇒ X,Y commute).
static void test_nseq_gpsplit_e2e_commute_tails() {
    std::cout << "test_nseq_gpsplit_e2e_commute_tails\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 300000;
    smt::context ctx(m, params);
    seq_util su(m);
    arith_util au(m);
    const expr_ref p(m.mk_const(symbol("p"), au.mk_int()), m);
    const expr_ref q(m.mk_const(symbol("q"), au.mk_int()), m);
    const expr_ref n(m.mk_const(symbol("n"), au.mk_int()), m);
    const expr_ref mm(m.mk_const(symbol("mm"), au.mk_int()), m);
    const expr_ref U(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")), p), m)), m);
    const expr_ref V(su.str.mk_concat(su.str.mk_string(zstring("a")),
                     expr_ref(su.str.mk_power(su.str.mk_string(zstring("bc")),
                              expr_ref(au.mk_mul(au.mk_int(2), q), m)), m)), m);
    const expr_ref X(su.str.mk_power(U, n), m);
    const expr_ref Y(su.str.mk_power(V, mm), m);
    const expr_ref lhs(su.str.mk_concat(X, Y), m);
    const expr_ref rhs(su.str.mk_concat(Y, X), m);
    for (expr* e : { p.get(), q.get(), n.get(), mm.get() })
        ctx.assert_expr(expr_ref(au.mk_ge(e, au.mk_int(1)), m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// helper: fully-ground equation, all listed vars >= 1, check verdict
static void gp_check(const char* label, expr* lhs, expr* rhs,
                     std::initializer_list<expr*> pos_vars, lbool expect,
                     ast_manager& m, arith_util& au, expr* extra = nullptr) {
    std::cout << label << "\n";
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 300000;
    smt::context ctx(m, params);
    for (expr* v : pos_vars)
        ctx.assert_expr(expr_ref(au.mk_ge(v, au.mk_int(1)), m));
    if (extra) ctx.assert_expr(expr_ref(extra, m));
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == expect);
    std::cout << (expect == l_true ? "  ok: sat\n" : "  ok: unsat\n");
}

// a^n·b^m = a^k·b^l → n=k ∧ m=l (multiple single-char power blocks).  SAT.
static void test_nseq_gp_anbm() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* k=m.mk_const(symbol("k"),au.mk_int()), *l=m.mk_const(symbol("l"),au.mk_int());
    expr* lhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("a")),n),
                               su.str.mk_power(su.str.mk_string(zstring("b")),mm));
    expr* rhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("a")),k),
                               su.str.mk_power(su.str.mk_string(zstring("b")),l));
    gp_check("test_nseq_gp_anbm", lhs, rhs, {n,mm,k,l}, l_true, m, au);
}

// (ab)^n·"x" = (abab)^m·"x" → n=2m (common root, tailed).  SAT.
static void test_nseq_gp_commonroot_tail() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* lhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("ab")),n), su.str.mk_string(zstring("x")));
    expr* rhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("abab")),mm), su.str.mk_string(zstring("x")));
    gp_check("test_nseq_gp_commonroot_tail", lhs, rhs, {n,mm}, l_true, m, au);
}

// (abab)^n = (ab)^m → m=2n (non-primitive base).  SAT.
static void test_nseq_gp_nonprim() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    gp_check("test_nseq_gp_nonprim", su.str.mk_power(su.str.mk_string(zstring("abab")),n),
             su.str.mk_power(su.str.mk_string(zstring("ab")),mm), {n,mm}, l_true, m, au);
}

// two power blocks of different nested bases:
// (a(bc)^p)^n·(a(de)^r)^k = (a(bc)^{2q})^m·(a(de)^s)^l → p=2q,n=m,r=s,k=l.  SAT.
static void test_nseq_gp_twoblocks() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    auto B=[&](const char* w, expr* x){ return su.str.mk_concat(su.str.mk_string(zstring("a")),
                                        su.str.mk_power(su.str.mk_string(zstring(w)), x)); };
    expr* p=m.mk_const(symbol("p"),au.mk_int()), *q=m.mk_const(symbol("q"),au.mk_int());
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* r=m.mk_const(symbol("r"),au.mk_int()), *s=m.mk_const(symbol("s"),au.mk_int());
    expr* k=m.mk_const(symbol("k"),au.mk_int()), *l=m.mk_const(symbol("l"),au.mk_int());
    expr* twoq=au.mk_mul(au.mk_int(2),q);
    expr* lhs=su.str.mk_concat(su.str.mk_power(B("bc",p),n), su.str.mk_power(B("de",r),k));
    expr* rhs=su.str.mk_concat(su.str.mk_power(B("bc",twoq),mm), su.str.mk_power(B("de",s),l));
    gp_check("test_nseq_gp_twoblocks", lhs, rhs, {p,q,n,mm,r,s,k,l}, l_true, m, au);
}

// ===================== 6 interesting fully-ground power benchmarks =====================
// Curated "greatest hits" from the fully-ground corpus, each showcasing a
// distinct behaviour that used to diverge or was previously unhandled.

// (1) A genuine CONJUGATION IDENTITY, true for ALL p,n:
//     a·((bc)^p·a)^n = (a·(bc)^p)^n·a          -> SAT (proved for symbolic p,n).
static void test_nseq_bench_conj_identity() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* p=m.mk_const(symbol("p"),au.mk_int()), *n=m.mk_const(symbol("n"),au.mk_int());
    expr* bcp=su.str.mk_power(su.str.mk_string(zstring("bc")),p);
    expr* lhs=su.str.mk_concat(su.str.mk_string(zstring("a")),
              su.str.mk_power(su.str.mk_concat(bcp, su.str.mk_string(zstring("a"))), n));
    expr* rhs=su.str.mk_concat(
              su.str.mk_power(su.str.mk_concat(su.str.mk_string(zstring("a")), bcp), n),
              su.str.mk_string(zstring("a")));
    gp_check("test_nseq_bench_conj_identity", lhs, rhs, {p,n}, l_true, m, au);
}

// (2) Char CONJUGATE that cannot commute: (ab)^n = (ba)^m, n,m>=1 -> UNSAT.
static void test_nseq_bench_charconj_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    gp_check("test_nseq_bench_charconj_unsat", su.str.mk_power(su.str.mk_string(zstring("ab")),n),
             su.str.mk_power(su.str.mk_string(zstring("ba")),mm), {n,mm}, l_false, m, au);
}

// (3) Different inner letters: (a·(bc)^p)^n = (a·(de)^q)^m, >=1 -> UNSAT.
static void test_nseq_bench_diffletters_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* p=m.mk_const(symbol("p"),au.mk_int()), *q=m.mk_const(symbol("q"),au.mk_int());
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* lhs=su.str.mk_power(su.str.mk_concat(su.str.mk_string(zstring("a")),
                              su.str.mk_power(su.str.mk_string(zstring("bc")),p)), n);
    expr* rhs=su.str.mk_power(su.str.mk_concat(su.str.mk_string(zstring("a")),
                              su.str.mk_power(su.str.mk_string(zstring("de")),q)), mm);
    gp_check("test_nseq_bench_diffletters_unsat", lhs, rhs, {p,q,n,mm}, l_false, m, au);
}

// (4) COMMON ROOT rebase: (ab)^n = (abab)^m  -> n = 2m  (SAT).
static void test_nseq_bench_commonroot() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    gp_check("test_nseq_bench_commonroot", su.str.mk_power(su.str.mk_string(zstring("ab")),n),
             su.str.mk_power(su.str.mk_string(zstring("abab")),mm), {n,mm}, l_true, m, au);
}

// (5) Power-sum IDENTITY: (ab)^n·(ab)^m = (ab)^{n+m}  -> SAT (all n,m).
static void test_nseq_bench_powsum_identity() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* lhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("ab")),n),
                               su.str.mk_power(su.str.mk_string(zstring("ab")),mm));
    expr* rhs=su.str.mk_power(su.str.mk_string(zstring("ab")), au.mk_add(n,mm));
    gp_check("test_nseq_bench_powsum_identity", lhs, rhs, {n,mm}, l_true, m, au);
}

// (6) Nested char-conjugate at a symbolic offset (pure):
//     (a·(bc)^p)^n = ((bc)^p·a)^m, n,m>=1 -> UNSAT (bases are conjugate, not equal).
static void test_nseq_bench_nestedconj_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* p=m.mk_const(symbol("p"),au.mk_int()), *n=m.mk_const(symbol("n"),au.mk_int());
    expr* mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* bcp=su.str.mk_power(su.str.mk_string(zstring("bc")),p);
    expr* lhs=su.str.mk_power(su.str.mk_concat(su.str.mk_string(zstring("a")), bcp), n);
    expr* rhs=su.str.mk_power(su.str.mk_concat(bcp, su.str.mk_string(zstring("a"))), mm);
    gp_check("test_nseq_bench_nestedconj_unsat", lhs, rhs, {p,n,mm}, l_false, m, au);
}

void tst_nseq_basic() {
    test_nseq_instantiation();
    test_nseq_param_validation();
    test_nseq_param_validation_rejects_invalid();
    test_nseq_simplification();
    test_nseq_node_satisfied();
    test_nseq_symbol_clash();
    test_nseq_var_eq_self();
    test_nseq_prefix_clash();
    test_nseq_const_nielsen_solvable();
    test_nseq_length_mismatch();
    test_setup_seq_str_dispatches_nseq();
    test_nseq_fine_wilf_e2e_unsat();
    test_nseq_fine_wilf_e2e_sat();
    test_nseq_fine_wilf_option_off();
    test_nseq_power_cursor_nested_e2e_unsat();
    test_nseq_power_cursor_nested_e2e_sat();
    test_nseq_power_normalize_e2e_sat();
    test_nseq_power_commute_e2e_sat();
    test_nseq_power_commute_e2e_unsat();
    test_nseq_gpsplit_e2e_sat();
    test_nseq_gpsplit_e2e_unsat();
    test_nseq_gpsplit_e2e_commute_tails();
    test_nseq_gp_anbm();
    test_nseq_gp_commonroot_tail();
    test_nseq_gp_nonprim();
    test_nseq_gp_twoblocks();
    // 6 curated interesting fully-ground power benchmarks
    test_nseq_bench_conj_identity();
    test_nseq_bench_charconj_unsat();
    test_nseq_bench_diffletters_unsat();
    test_nseq_bench_commonroot();
    test_nseq_bench_powsum_identity();
    test_nseq_bench_nestedconj_unsat();
    std::cout << "nseq_basic: all tests passed\n";
}
