
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/proofs/proof_checker.h"
#include "ast/ast_ll_pp.h"
#include "ast/reg_decl_plugins.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

void tst_checker1() {
    ast_manager m(PGM_ENABLED);
    expr_ref a(m);
    proof_ref p1(m), p2(m), p3(m), p4(m);
    expr_ref_vector side_conditions(m);

    a = m.mk_const(symbol("a"), m.mk_bool_sort());
    p1 = m.mk_hypothesis(a.get());
    p2 = m.mk_hypothesis(m.mk_not(a.get()));
    ast_ll_pp(std::cout, m, p1.get());
    ast_ll_pp(std::cout, m, p2.get());
    proof* proofs[2] = { p1.get(), p2.get() };
    p3 = m.mk_unit_resolution(2, proofs);
    p4 = m.mk_lemma(p3.get(), a.get());
    ast_ll_pp(std::cout, m, p4.get());
    proof_checker checker(m);
    p4 = m.mk_lemma(p3.get(), m.mk_or(a.get(), m.mk_not(a.get())));
    ast_ll_pp(std::cout, m, p4.get());
    VERIFY(checker.check(p4.get(), side_conditions));
}

void tst_initializer_list_overloads() {
    ast_manager m(PGM_ENABLED);
    expr_ref a(m), b(m);
    proof_ref p1(m), p2(m), p3(m), p4(m);
    expr_ref_vector side_conditions(m);

    // Test mk_unit_resolution with initializer_list
    a = m.mk_const(symbol("a"), m.mk_bool_sort());
    b = m.mk_const(symbol("b"), m.mk_bool_sort());
    p1 = m.mk_hypothesis(a.get());
    p2 = m.mk_hypothesis(m.mk_not(a.get()));
    
    // Test the new initializer_list overload - should produce false
    p3 = m.mk_unit_resolution({ p1.get(), p2.get() });
    VERIFY(m.get_fact(p3.get()) == m.mk_false());
    
    // Test mk_unit_resolution with new_fact parameter
    expr_ref fact(m.mk_or(a.get(), b.get()), m);
    proof_ref pa_or_b(m.mk_hypothesis(fact.get()), m);
    proof_ref pnot_a(m.mk_hypothesis(m.mk_not(a.get())), m);
    p4 = m.mk_unit_resolution({ pa_or_b.get(), pnot_a.get() }, b.get());
    VERIFY(m.get_fact(p4.get()) == b.get());
    
    // Test mk_transitivity with initializer_list
    // Create a simple transitivity chain: a = b, b = c => a = c
    expr_ref c(m);
    c = m.mk_const(symbol("c"), m.mk_bool_sort());
    
    // Create rewrite proofs for a = b and b = c
    proof_ref pr_ab(m.mk_rewrite(a.get(), b.get()), m);
    proof_ref pr_bc(m.mk_rewrite(b.get(), c.get()), m);
    
    // Test the new initializer_list overload for transitivity
    // This should create a proof of a = c
    proof_ref p5(m.mk_transitivity({ pr_ab.get(), pr_bc.get() }), m);
    VERIFY(p5.get() != nullptr);
    // Verify the result is a proof with the expected fact (a = c)
    expr* trans_fact = m.get_fact(p5.get());
    VERIFY(m.is_eq(trans_fact));
    VERIFY(to_app(trans_fact)->get_arg(0) == a.get());
    VERIFY(to_app(trans_fact)->get_arg(1) == c.get());
    
    std::cout << "Initializer list overloads test passed!" << std::endl;
}

static void tst_euf_negation() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::theory_checker checker(m);
    expr_ref x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
    expr_ref y(m.mk_const(symbol("y"), m.mk_bool_sort()), m);
    expr_ref nx(m.mk_not(x), m);
    expr_ref eq(m.mk_eq(nx, y), m);
    auto check = [&](std::initializer_list<expr*> args) {
        expr_ref hint(m.mk_app(symbol("euf"), args.size(), args.begin(), m.mk_proof_sort()), m);
        return checker.check(hint);
    };

    VERIFY(check({m.mk_eq(x, nx)}));
    VERIFY(!check({eq, y}));
    VERIFY(check({x, eq, y}));
    VERIFY(!check({x, eq, m.mk_not(y)}));
    VERIFY(check({nx, eq, m.mk_not(y)}));
    VERIFY(!check({nx, eq, y}));
}

static void tst_euf_negation_large_classes() {
    ast_manager m;
    reg_decl_plugins(m);
    euf::theory_checker checker(m);
    expr_ref x(m.mk_const(symbol("x"), m.mk_bool_sort()), m);
    expr_ref nx(m.mk_not(x), m);
    expr_ref_vector args(m);
    // Both classes lack truth values, so per-negation class scans are quadratic.
    for (unsigned i = 0; i < 16384; ++i) {
        expr_ref y(m.mk_fresh_const("y", m.mk_bool_sort()), m);
        args.push_back(m.mk_eq(x, y));
        args.push_back(m.mk_eq(nx, m.mk_not(y)));
    }
    expr_ref hint(m.mk_app(symbol("euf"), args.size(), args.data(), m.mk_proof_sort()), m);
    VERIFY(!checker.check(hint));
    args.push_back(m.mk_false());
    hint = m.mk_app(symbol("euf"), args.size(), args.data(), m.mk_proof_sort());
    VERIFY(checker.check(hint));
}

// Exercises the `PR_BIND`/`PR_QUANT_INTRO` case of `check1_basic`: the
// lambda-wrapped shape `rewriter_tpl::process_quantifier` actually
// constructs (`mk_quant_intro(q1, q2, mk_bind_proof(q1, p0))`, where `p0`
// is a proof of `q1`'s body = `q2`'s body). A genuine instance must be
// accepted.
//
// (A *tampered* instance -- one whose claimed outer quantifiers don't
// match what the wrapped inner proof `p0` actually establishes -- is
// now rejected too, where previously `check1_basic` only tested
// `is_lambda(...)` without ever inspecting `p0`, so a mismatched claim
// like this was accepted unconditionally. That negative case isn't
// exercised here as an automated regression test: like every other
// malformed-shape case in this function, rejection goes through
// `UNREACHABLE()`, which aborts the process by design rather than
// returning `false` -- consistent with the rest of `check1_basic`
// treating a malformed proof as an internal invariant violation, not
// recoverable bad input. Manually confirmed during development: giving
// `mk_quant_intro` a `q2` whose body isn't what `p0` proves now hits
// that same `UNREACHABLE()` path instead of silently returning `true`.)
static void tst_quant_intro() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    sort_ref B(m.mk_bool_sort(), m);
    sort* Bs = B.get();
    func_decl_ref f(m.mk_func_decl(symbol("f"), B, B, func_decl_info()), m);
    func_decl_ref g(m.mk_func_decl(symbol("g"), B, B, func_decl_info()), m);
    expr_ref var0(m.mk_var(0, B), m);
    expr_ref body1(m.mk_app(f, var0.get()), m);
    expr_ref body2(m.mk_app(g, var0.get()), m);
    symbol xname("x");

    proof_checker checker(m);
    expr_ref_vector side_conditions(m);

    // Genuine: q1 = forall x. f(x), q2 = forall x. g(x), and p0 really is
    // a proof of f(x) = g(x).
    quantifier_ref q1(m.mk_forall(1, &Bs, &xname, body1.get()), m);
    quantifier_ref q2(m.mk_forall(1, &Bs, &xname, body2.get()), m);
    proof_ref p0(m.mk_rewrite(body1.get(), body2.get()), m);
    proof_ref p_bind(m.mk_bind_proof(q1.get(), p0.get()), m);
    proof_ref p_qi(m.mk_quant_intro(q1.get(), q2.get(), p_bind.get()), m);
    VERIFY(checker.check(p_qi.get(), side_conditions));
}

// Exercises the `PR_PUSH_QUANT` case of `check1_basic`: the shape
// `distribute_forall_simplifier::rw_cfg::reduce_quantifier` actually
// constructs via `mk_push_quant(old_q, result)`, for both
// `(forall X (and F1 .. Fn)) <-> (and (forall X F1) .. (forall X Fn))`
// and `(exists X (or F1 .. Fn)) <-> (or (exists X F1) .. (exists X Fn))`.
// Prior to this fix, `check1_basic`'s `PR_PUSH_QUANT` case had no
// `return true` on the success path at all (it fell through to the
// shared `UNREACHABLE(); return false;` tail unconditionally), so *every*
// `PR_PUSH_QUANT` proof -- even a well-formed one -- was rejected; and it
// only ever matched the `and`-shaped case, so the `exists`/`or` shape
// that `distribute_forall_simplifier` also produces was entirely
// unhandled.
static void tst_push_quant() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    sort_ref B(m.mk_bool_sort(), m);
    sort* Bs = B.get();
    func_decl_ref f(m.mk_func_decl(symbol("f"), B, B, func_decl_info()), m);
    func_decl_ref g(m.mk_func_decl(symbol("g"), B, B, func_decl_info()), m);
    expr_ref var0(m.mk_var(0, B), m);
    expr_ref f0(m.mk_app(f, var0.get()), m);
    expr_ref g0(m.mk_app(g, var0.get()), m);
    symbol xname("x");

    proof_checker checker(m);
    expr_ref_vector side_conditions(m);

    // (forall x (and (f x) (g x))) <-> (and (forall x (f x)) (forall x (g x)))
    {
        expr_ref body(m.mk_and(f0.get(), g0.get()), m);
        quantifier_ref q(m.mk_forall(1, &Bs, &xname, body.get()), m);
        quantifier_ref qf(m.mk_forall(1, &Bs, &xname, f0.get()), m);
        quantifier_ref qg(m.mk_forall(1, &Bs, &xname, g0.get()), m);
        expr_ref result(m.mk_and(qf.get(), qg.get()), m);
        proof_ref pr(m.mk_push_quant(q.get(), result.get()), m);
        VERIFY(checker.check(pr.get(), side_conditions));
    }

    // (exists x (or (f x) (g x))) <-> (or (exists x (f x)) (exists x (g x)))
    {
        expr_ref body(m.mk_or(f0.get(), g0.get()), m);
        quantifier_ref q(m.mk_exists(1, &Bs, &xname, body.get()), m);
        quantifier_ref qf(m.mk_exists(1, &Bs, &xname, f0.get()), m);
        quantifier_ref qg(m.mk_exists(1, &Bs, &xname, g0.get()), m);
        expr_ref result(m.mk_or(qf.get(), qg.get()), m);
        proof_ref pr(m.mk_push_quant(q.get(), result.get()), m);
        VERIFY(checker.check(pr.get(), side_conditions));
    }
}

// Exercises the new `PR_DEMODULATION` rule: `t1 = t2` justified by premise
// proofs of `l_i = r_i` (i = 1..n), where `t2` is obtained from `t1` by
// simultaneously replacing every occurrence of `l_i` by `r_i`. Unlike
// `PR_REWRITE`/`PR_REWRITE_STAR` (which the checker trusts as a side
// condition without verifying the substitution), `PR_DEMODULATION` is
// actually re-derived inside `check1_basic` via `expr_safe_replace` and
// compared structurally against the claimed result.
static void tst_demodulation() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    sort_ref B(m.mk_bool_sort(), m);
    func_decl_ref f(m.mk_func_decl(symbol("f"), B, B, B, func_decl_info()), m);
    func_decl_ref p(m.mk_func_decl(symbol("p"), B, B), m);
    expr_ref a(m.mk_const(symbol("a"), B), m);
    expr_ref b(m.mk_const(symbol("b"), B), m);
    expr_ref c(m.mk_const(symbol("c"), B), m);
    expr_ref d(m.mk_const(symbol("d"), B), m);

    proof_checker checker(m);
    expr_ref_vector side_conditions(m);

    // Single equation: t1 = p(f(a, a)), t2 = p(f(b, b)) via a = b.
    {
        proof_ref eq_ab(m.mk_rewrite(a.get(), b.get()), m);
        expr_ref t1(m.mk_app(p, m.mk_app(f, a.get(), a.get())), m);
        expr_ref t2(m.mk_app(p, m.mk_app(f, b.get(), b.get())), m);
        proof* eqs[1] = { eq_ab.get() };
        proof_ref pr(m.mk_demodulation(t1.get(), t2.get(), 1, eqs), m);
        VERIFY(checker.check(pr.get(), side_conditions));
    }

    // Simultaneous equations: t1 = f(a, c), t2 = f(b, d) via a = b, c = d.
    {
        proof_ref eq_ab(m.mk_rewrite(a.get(), b.get()), m);
        proof_ref eq_cd(m.mk_rewrite(c.get(), d.get()), m);
        expr_ref t1(m.mk_app(f, a.get(), c.get()), m);
        expr_ref t2(m.mk_app(f, b.get(), d.get()), m);
        proof* eqs[2] = { eq_ab.get(), eq_cd.get() };
        proof_ref pr(m.mk_demodulation(t1.get(), t2.get(), 2, eqs), m);
        VERIFY(checker.check(pr.get(), side_conditions));
    }

    // Zero equations degenerates to a plain rewrite (t1 == t2 verbatim).
    {
        expr_ref t1(m.mk_app(p, a.get()), m);
        proof_ref pr(m.mk_demodulation(t1.get(), t1.get(), 0, nullptr), m);
        VERIFY(checker.check(pr.get(), side_conditions));
    }
}

void tst_proof_checker() {
    tst_checker1();
    tst_initializer_list_overloads();
    tst_euf_negation();
    tst_euf_negation_large_classes();
    tst_quant_intro();
    tst_push_quant();
    tst_demodulation();
}
