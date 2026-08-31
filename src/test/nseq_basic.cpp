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
// EqSplit: decomposition of a word equation at an interior split point
// -----------------------------------------------------------------------

// Asserts  "a"·z·z·y  ==  y·y·z·"ba"  into ctx.  The equation is UNSAT
// (verified by exhaustive search over {a,b} — two letters are WLOG, since the
// morphism fixing a and b collapses any larger alphabet onto them), but no
// prefix/suffix cancellation applies and the length identity |z| = |y| + 1 is
// perfectly satisfiable, so the refutation has to come from an *interior*
// alignment.  eq_split supplies one: it cuts both sides at a boundary where
// the two prefixes carry equal variable multisets.
static void assert_eq_split_eq(smt::context& ctx, ast_manager& m) {
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref y(m.mk_const(symbol("y"), str_sort), m);
    const expr_ref z(m.mk_const(symbol("z"), str_sort), m);

    expr_ref lhs(su.str.mk_concat(su.str.mk_string(zstring("a")), z), m);
    lhs = su.str.mk_concat(lhs, z);
    lhs = su.str.mk_concat(lhs, y);

    expr_ref rhs(su.str.mk_concat(y, y), m);
    rhs = su.str.mk_concat(rhs, z);
    rhs = su.str.mk_concat(rhs, su.str.mk_string(zstring("ba")));

    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
}

// UNSAT, and reached only because eq_split fires: the modifier spent a long
// time unable to execute at all (its split condition was unsatisfiable), and
// without it the Nielsen search diverges on this equation — 8000+ nodes and
// still running after a minute.  This is the regression test for that.
static void test_nseq_eq_split_e2e_unsat() {
    std::cout << "test_nseq_eq_split_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    smt::context ctx(m, params);
    assert_eq_split_eq(ctx, m);
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// eq_split must not refute a satisfiable equation.  x·"ab"·y == y·"ab"·x is
// solved by x = y (in particular x = y = ""), yet it offers split points on
// both sides together with a syntactically zero length identity — the
// configuration in which the split is least constrained, and the one in which
// an off-by-one in which side receives the padding shows up as sat -> unsat.
static void test_nseq_eq_split_sat_guard() {
    std::cout << "test_nseq_eq_split_sat_guard\n";
    ast_manager m;
    reg_decl_plugins(m);
    seq_util su(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    smt::context ctx(m, params);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref x(m.mk_const(symbol("x"), str_sort), m);
    const expr_ref y(m.mk_const(symbol("y"), str_sort), m);
    expr_ref lhs(su.str.mk_concat(x, su.str.mk_string(zstring("ab"))), m);
    lhs = su.str.mk_concat(lhs, y);
    expr_ref rhs(su.str.mk_concat(y, su.str.mk_string(zstring("ab"))), m);
    rhs = su.str.mk_concat(rhs, x);
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// A split point may not sit at either side's endpoint: the "prefix" would be
// the whole side and the suffix empty, so the first new equation is just the
// original with a renamed tail.  eq_split emits a single progress child, so
// that child re-derives its own parent and the node is closed as unsat by the
// memo.  "a"·z == z·"a" is satisfiable (z = "" among others) and was reported
// unsat while such splits were accepted.
static void test_nseq_eq_split_no_endpoint_split() {
    std::cout << "test_nseq_eq_split_no_endpoint_split\n";
    ast_manager m;
    reg_decl_plugins(m);
    seq_util su(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    smt::context ctx(m, params);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref z(m.mk_const(symbol("z"), str_sort), m);
    const expr_ref lhs(su.str.mk_concat(su.str.mk_string(zstring("a")), z), m);
    const expr_ref rhs(su.str.mk_concat(z, su.str.mk_string(zstring("a"))), m);
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// The DFS node budget (smt.nseq.max_nodes) must make the search give up.
//
// search_dfs returns unknown both when the *per-iteration* depth bound is hit
// and when the *global* node budget is spent, and the iterative-deepening loop
// used to treat every unknown as the former: double the bound and retry.  The
// node budget only ever grows, so each retry re-tripped it on the first node
// and the loop spun until the external timeout -- reporting "timeout" after
// burning the full time budget instead of "unknown" after 500 nodes.
//
// b·z·y·y = y·y·z·a is a divergent instance (nseq does not terminate on it),
// so this test hangs forever rather than failing if the regression returns:
// with no resource limit set there is nothing to break the spin.
static void test_nseq_max_nodes_gives_up() {
    std::cout << "test_nseq_max_nodes_gives_up\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    SASSERT(params.m_nseq_max_nodes == 0); // default: unlimited
    params.m_nseq_max_nodes = 500;
    smt::context ctx(m, params);
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref y(m.mk_const(symbol("y"), str_sort), m);
    const expr_ref z(m.mk_const(symbol("z"), str_sort), m);
    const expr_ref lhs(
        su.str.mk_concat(su.str.mk_concat(su.str.mk_string(zstring("b")), z),
                         su.str.mk_concat(y, y)), m);
    const expr_ref rhs(
        su.str.mk_concat(su.str.mk_concat(y, y),
                         su.str.mk_concat(z, su.str.mk_string(zstring("a")))), m);
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
    const lbool r = ctx.check();
    SASSERT(r == l_undef);
    std::cout << "  ok: unknown\n";
}

// The abelian (per-letter count) rule.  b·z·y·y == y·y·z·a is the canonical
// case where nseq diverges: the two sides have identical length, the free z
// keeps the constants from ever meeting, and substituting y -> b·y' adds a
// constant to both occurrences on each side while only one cancels, so the
// equation grows by two constants per peel and no state ever repeats.  Every
// variable occurs equally often on both sides, so the length row degenerates
// to 0 = 0 -- but letter 'a' alone gives 0 = 1.
static void assert_abelian_eq(smt::context& ctx, ast_manager& m,
                              char const* lhs_head, char const* rhs_tail) {
    seq_util su(m);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref y(m.mk_const(symbol("y"), str_sort), m);
    const expr_ref z(m.mk_const(symbol("z"), str_sort), m);
    const expr_ref lhs(
        su.str.mk_concat(su.str.mk_concat(su.str.mk_string(zstring(lhs_head)), z),
                         su.str.mk_concat(y, y)), m);
    const expr_ref rhs(
        su.str.mk_concat(su.str.mk_concat(y, y),
                         su.str.mk_concat(z, su.str.mk_string(zstring(rhs_tail)))), m);
    ctx.assert_expr(expr_ref(m.mk_eq(lhs, rhs), m));
}

static void test_nseq_abelian_e2e_unsat() {
    std::cout << "test_nseq_abelian_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    SASSERT(!params.m_nseq_abelian); // opt-in
    params.m_nseq_abelian = true;
    smt::context ctx(m, params);
    assert_abelian_eq(ctx, m, "b", "a");
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// Same shape with multi-character literals, so the scan has to count inside a
// zstring rather than only over single units.  "ab" vs "aa" balances in total
// length (and even in the 'a' count of the length row) but not per letter.
static void test_nseq_abelian_multichar_unsat() {
    std::cout << "test_nseq_abelian_multichar_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_abelian = true;
    smt::context ctx(m, params);
    assert_abelian_eq(ctx, m, "ab", "aa");
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// The rule must not over-refute.  Making the two literals agree turns the same
// shape satisfiable (y = z = ""), and every letter now balances, so the abelian
// check has to stay silent.
static void test_nseq_abelian_sat_guard() {
    std::cout << "test_nseq_abelian_sat_guard\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_abelian = true;
    smt::context ctx(m, params);
    assert_abelian_eq(ctx, m, "b", "b");
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// ... and with the option off the same instance is undecided, which is what
// makes the refutation above attributable to the rule rather than to some
// other pass.  A node budget is needed only to make the divergence terminate.
static void test_nseq_abelian_option_off() {
    std::cout << "test_nseq_abelian_option_off\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_max_nodes = 500;
    smt::context ctx(m, params);
    assert_abelian_eq(ctx, m, "b", "a");
    const lbool r = ctx.check();
    SASSERT(r == l_undef);
    std::cout << "  ok: unknown\n";
}

// The per-letter congruence rule over regex memberships.  The shape below is
// the generated split_membership family in miniature: every constraint is a
// membership, there is no word equation anywhere -- so the abelian rule above,
// and any abstraction hooked to the equation store, sees nothing at all -- and
// the languages encode "#a is even" / "#a is odd" through the camouflage idiom
//
//     (re.inter re.allchar (re.comp (str.to_re "a")))      any character but a
//
// which is exactly what a count-only Parikh abstraction cannot see through:
// complement forces it to the full set, since a word and its permutations
// share a count.  These tests therefore also pin the length refinement that
// makes the abstraction non-vacuous -- drop it and `even` abstracts to "any
// number of a's" and nothing is refuted.
namespace {
    struct mod2_langs {
        ast_manager& m;
        seq_util     su;
        expr_ref     m_even, m_odd;

        explicit mod2_langs(ast_manager& mgr) : m(mgr), su(mgr), m_even(mgr), m_odd(mgr) {
            const expr_ref a(su.re.mk_to_re(su.str.mk_string(zstring("a"))), m);
            sort* re_sort = a->get_sort();
            const expr_ref na(su.re.mk_inter(su.re.mk_full_char(re_sort),
                                             su.re.mk_complement(a)), m);
            const expr_ref nas(su.re.mk_star(na), m);
            // (a · [^a]*){2,2} repeated: blocks contributing exactly two a's each
            const expr_ref blk(
                su.re.mk_star(su.re.mk_loop(su.re.mk_concat(a, nas), 2, 2)), m);
            m_even = su.re.mk_concat(nas, blk);
            m_odd = su.re.mk_concat(su.re.mk_concat(nas, su.re.mk_concat(a, nas)), blk);
        }
    };
}

// x ∈ even, y ∈ odd, x·y ∈ even.  Counting a's modulo 2 gives 0 + 1 ≡ 0,
// which is false, and no other reasoning is needed.
static void assert_mod2_memberships(smt::context& ctx, ast_manager& m, bool y_is_odd) {
    seq_util su(m);
    const mod2_langs lang(m);
    sort* str_sort = su.str.mk_string_sort();
    const expr_ref x(m.mk_const(symbol("x"), str_sort), m);
    const expr_ref y(m.mk_const(symbol("y"), str_sort), m);
    ctx.assert_expr(expr_ref(su.re.mk_in_re(x, lang.m_even), m));
    ctx.assert_expr(expr_ref(su.re.mk_in_re(y, y_is_odd ? lang.m_odd : lang.m_even), m));
    ctx.assert_expr(expr_ref(su.re.mk_in_re(su.str.mk_concat(x, y), lang.m_even), m));
}

static void test_nseq_regex_parikh_e2e_unsat() {
    std::cout << "test_nseq_regex_parikh_e2e_unsat\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    SASSERT(!params.m_nseq_regex_parikh); // opt-in
    params.m_nseq_regex_parikh = true;
    smt::context ctx(m, params);
    assert_mod2_memberships(ctx, m, true);
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat\n";
}

// The rule must not over-refute: making both variables even leaves the system
// solvable (x = y = ""), so the check has to stay silent and the instance is
// satisfiable.
static void test_nseq_regex_parikh_sat_guard() {
    std::cout << "test_nseq_regex_parikh_sat_guard\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_regex_parikh = true;
    smt::context ctx(m, params);
    assert_mod2_memberships(ctx, m, false);
    const lbool r = ctx.check();
    SASSERT(r == l_true);
    std::cout << "  ok: sat\n";
}

// A modulus bound below the one the instance needs must not refute: with
// max modulus 2 the rule sees "#a mod 2", which is exactly what this instance
// needs, so raise the requirement to 3 a's and check the bound is honoured.
static void test_nseq_regex_parikh_residues() {
    std::cout << "test_nseq_regex_parikh_residues\n";
    ast_manager m;
    reg_decl_plugins(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    params.m_nseq_regex_parikh = true;
    params.m_nseq_regex_parikh_mod = 2;
    smt::context ctx(m, params);
    assert_mod2_memberships(ctx, m, true);
    const lbool r = ctx.check();
    SASSERT(r == l_false);
    std::cout << "  ok: unsat at modulus 2\n";
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
    test_nseq_eq_split_e2e_unsat();
    test_nseq_eq_split_sat_guard();
    test_nseq_eq_split_no_endpoint_split();
    test_nseq_max_nodes_gives_up();
    test_nseq_abelian_e2e_unsat();
    test_nseq_abelian_multichar_unsat();
    test_nseq_abelian_sat_guard();
    test_nseq_abelian_option_off();
    test_nseq_regex_parikh_e2e_unsat();
    test_nseq_regex_parikh_sat_guard();
    test_nseq_regex_parikh_residues();
    std::cout << "nseq_basic: all tests passed\n";
}
