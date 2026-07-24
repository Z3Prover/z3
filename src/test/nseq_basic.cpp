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

// helper: assert a fully-ground equation with all listed vars >= 1 and check verdict
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

// a^n·b^m = a^k·b^l  → n=k ∧ m=l (multiple single-char power blocks).  SAT.
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

// (ab)^n·"x" = (abab)^m·"x"  → n=2m (common root, tailed).  SAT.
static void test_nseq_gp_commonroot_tail() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    expr* lhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("ab")),n), su.str.mk_string(zstring("x")));
    expr* rhs=su.str.mk_concat(su.str.mk_power(su.str.mk_string(zstring("abab")),mm), su.str.mk_string(zstring("x")));
    gp_check("test_nseq_gp_commonroot_tail", lhs, rhs, {n,mm}, l_true, m, au);
}

// (abab)^n = (ab)^m  → m=2n (non-primitive base).  SAT.
static void test_nseq_gp_nonprim() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    expr* n=m.mk_const(symbol("n"),au.mk_int()), *mm=m.mk_const(symbol("mm"),au.mk_int());
    gp_check("test_nseq_gp_nonprim", su.str.mk_power(su.str.mk_string(zstring("abab")),n),
             su.str.mk_power(su.str.mk_string(zstring("ab")),mm), {n,mm}, l_true, m, au);
}

// two power blocks of different nested bases:
// (a(bc)^p)^n·(a(de)^r)^k = (a(bc)^{2q})^m·(a(de)^s)^l  → p=2q,n=m,r=s,k=l.  SAT.
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

// -----------------------------------------------------------------------
// str.replace end-to-end tests (full smt::context, real arithmetic).
//
// The Nielsen replace modifiers (apply_replace_epsilon /
// apply_const_nielsen_replace / apply_var_nielsen_replace /
// apply_replace_replace, priority 3c-3c4) decompose a symbolic str.replace at
// the head of a word equation.  These tests assert replace-based formulas into
// a real nseq context, check the verdict, and — on sat — validate that the
// produced model actually satisfies every assertion.  Two "give-up" cases must
// return unknown (l_undef) rather than an unsound answer.  Mirrors the .smt2
// suite in nseq_replace_tests/.
// -----------------------------------------------------------------------

static void replace_check(const char* label, ast_manager& m,
                          expr_ref_vector const& assertions, lbool expect,
                          unsigned max_nodes = 200000) {
    std::cout << label << "\n";
    smt_params params;
    params.m_string_solver = symbol("nseq");
    // A bounded node budget makes solve() return unknown (rather than run unbounded) on
    // the cases nseq cannot decide — the unit-test harness has no timeout.
    params.m_nseq_max_nodes = max_nodes;
    smt::context ctx(m, params);
    for (expr* a : assertions)
        ctx.assert_expr(a);
    const lbool r = ctx.check();
    SASSERT(r == expect);
    if (r != expect) {
        std::cerr << "  FAIL: expected " << expect << " got " << r << "\n";
        return;
    }
    if (r == l_true) {
        model_ref mdl;
        ctx.get_model(mdl);
        SASSERT(mdl);
        // the model must satisfy every asserted formula (guards against an
        // invalid model / spurious sat)
        if (!mdl->is_true(assertions)) {
            std::cerr << "  FAIL: model does not satisfy the assertions\n";
            SASSERT(false && "invalid model produced by nseq for str.replace");
        }
        std::cout << "  ok: sat, model validated\n";
    }
    else if (r == l_false)
        std::cout << "  ok: unsat\n";
    else
        std::cout << "  ok: unknown (sound give-up)\n";
}

// SAT: replace vanishes (s=""), the leading char of u matches.
static void test_nseq_replace_empty_side() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *u = m.mk_const(symbol("u"), ss), *v = m.mk_const(symbol("v"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("b"))), u);
    expr* rhs = su.str.mk_concat(su.str.mk_string(zstring("b")), v);
    expr_ref_vector a(m); a.push_back(m.mk_eq(lhs, rhs));
    replace_check("test_nseq_replace_empty_side", m, a, l_true);
}

// SAT: s starts with src -> the replace rewrites the leading run (starts-with elim).
static void test_nseq_replace_starts_with() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *u = m.mk_const(symbol("u"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("XY"))), u);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, su.str.mk_string(zstring("XYZ"))));
    a.push_back(su.str.mk_prefix(su.str.mk_string(zstring("a")), s));   // prefixof("a", s)
    replace_check("test_nseq_replace_starts_with", m, a, l_true);
}

// SAT: s does not start with src -> leading char preserved (char peel).
static void test_nseq_replace_not_starts_with() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *u = m.mk_const(symbol("u"), ss), *v = m.mk_const(symbol("v"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("b"))), u);
    expr* rhs = su.str.mk_concat(su.str.mk_string(zstring("z")), v);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, rhs));
    a.push_back(su.str.mk_prefix(su.str.mk_string(zstring("z")), s));
    a.push_back(au.mk_gt(su.str.mk_length(s), au.mk_int(2)));
    replace_check("test_nseq_replace_not_starts_with", m, a, l_true);
}

// SAT: deletion of the first occurrence (dst = "").
static void test_nseq_replace_delete() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(su.str.mk_replace(s, su.str.mk_string(zstring("ab")), su.str.mk_string(zstring(""))),
                        su.str.mk_string(zstring("cd"))));
    a.push_back(m.mk_eq(su.str.mk_length(s), au.mk_int(4)));
    replace_check("test_nseq_replace_delete", m, a, l_true);
}

// SAT: replace head vs a string variable head.
static void test_nseq_replace_vs_var() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *x = m.mk_const(symbol("x"), ss);
    expr* u = m.mk_const(symbol("u"), ss), *v = m.mk_const(symbol("v"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("ab")), su.str.mk_string(zstring("c"))), u);
    expr* rhs = su.str.mk_concat(x, v);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, rhs));
    a.push_back(m.mk_eq(x, su.str.mk_string(zstring("c"))));
    a.push_back(au.mk_gt(su.str.mk_length(s), au.mk_int(1)));
    replace_check("test_nseq_replace_vs_var", m, a, l_true);
}

// SAT: two replace heads, both inputs non-empty (apply_replace_replace).
static void test_nseq_replace_vs_replace() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *t = m.mk_const(symbol("t"), ss);
    expr* u = m.mk_const(symbol("u"), ss), *v = m.mk_const(symbol("v"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("b"))), u);
    expr* rhs = su.str.mk_concat(su.str.mk_replace(t, su.str.mk_string(zstring("c")), su.str.mk_string(zstring("d"))), v);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, rhs));
    a.push_back(au.mk_gt(su.str.mk_length(s), au.mk_int(0)));
    a.push_back(au.mk_gt(su.str.mk_length(t), au.mk_int(0)));
    replace_check("test_nseq_replace_vs_replace", m, a, l_true);
}

// UNSAT: replace(s,a,b) = s but s starts with a — the first a becomes b.
static void test_nseq_replace_fixpoint_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("b"))), s));
    a.push_back(su.str.mk_prefix(su.str.mk_string(zstring("a")), s));
    replace_check("test_nseq_replace_fixpoint_unsat", m, a, l_false);
}

// A non-self-referential UNSAT clash: s starts with "a" ⇒ replace(s,"a","b") begins with
// "b", which must equal a leading "c".
static void test_nseq_replace_clash_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *u = m.mk_const(symbol("u"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("b"))), u);
    expr* rhs = su.str.mk_concat(su.str.mk_string(zstring("c")), u);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, rhs));
    a.push_back(su.str.mk_prefix(su.str.mk_string(zstring("a")), s));
    replace_check("test_nseq_replace_clash_unsat", m, a, l_false);
}

// UNSAT: fully determined by s = "hello", wrong target.
static void test_nseq_replace_concrete_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(s, su.str.mk_string(zstring("hello"))));
    a.push_back(m.mk_eq(su.str.mk_replace(s, su.str.mk_string(zstring("l")), su.str.mk_string(zstring("L"))),
                        su.str.mk_string(zstring("xyz"))));
    replace_check("test_nseq_replace_concrete_unsat", m, a, l_false);
}

// UNSAT via the lazy length axiom: the replace occurs only inside str.len (the
// modifiers never decompose it), but ensure_replace_length_axioms contributes its
// contains-based length.  s starts with "a" ⇒ the first "a"->"bb" grows the length by
// 1, so |replace| = |s|+1 ≠ |s|.
static void test_nseq_replace_len_only_unsat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss);
    expr_ref_vector a(m);
    a.push_back(su.str.mk_prefix(su.str.mk_string(zstring("a")), s));
    a.push_back(m.mk_eq(su.str.mk_length(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("bb")))),
                        su.str.mk_length(s)));
    replace_check("test_nseq_replace_len_only_unsat", m, a, l_false, 20000);
}

// SAT: a replace whose defining variable is unused is a don't-care — the length
// axiom constrains its length harmlessly and any value works (models the slog /
// Stranger sanitizer benchmarks where x = replace(input, pattern, "") and x is dead).
static void test_nseq_replace_dead_definition_sat() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* in = m.mk_const(symbol("in"), ss), *x = m.mk_const(symbol("x_dead"), ss), *y = m.mk_const(symbol("y"), ss);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(x, su.str.mk_replace(in, su.str.mk_string(zstring("ab")), su.str.mk_string(zstring("")))));
    a.push_back(m.mk_eq(y, su.str.mk_string(zstring("hello"))));   // x is never used
    replace_check("test_nseq_replace_dead_definition_sat", m, a, l_true);
}

// GIVE-UP (unknown): str.at(s,0) decomposes s via nth/tail while replace(s,..)
// also decomposes s; the two decompositions can't be reconciled, so nseq gives
// up rather than emit an invalid model.
static void test_nseq_replace_at_same_var_giveup() {
    ast_manager m; reg_decl_plugins(m); seq_util su(m); arith_util au(m);
    sort* ss = su.str.mk_string_sort();
    expr* s = m.mk_const(symbol("s"), ss), *u = m.mk_const(symbol("u"), ss);
    expr* lhs = su.str.mk_concat(su.str.mk_replace(s, su.str.mk_string(zstring("a")), su.str.mk_string(zstring("XY"))), u);
    expr_ref_vector a(m);
    a.push_back(m.mk_eq(lhs, su.str.mk_string(zstring("XYZ"))));
    a.push_back(m.mk_eq(su.str.mk_at(s, au.mk_int(0)), su.str.mk_string(zstring("a"))));
    replace_check("test_nseq_replace_at_same_var_giveup", m, a, l_undef, 3000);
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
    // str.replace modifiers
    test_nseq_replace_empty_side();
    test_nseq_replace_starts_with();
    test_nseq_replace_not_starts_with();
    test_nseq_replace_delete();
    test_nseq_replace_vs_var();
    test_nseq_replace_vs_replace();
    test_nseq_replace_fixpoint_unsat();
    test_nseq_replace_clash_unsat();
    test_nseq_replace_concrete_unsat();
    test_nseq_replace_len_only_unsat();
    test_nseq_replace_dead_definition_sat();
    test_nseq_replace_at_same_var_giveup();
    std::cout << "nseq_basic: all tests passed\n";
}
