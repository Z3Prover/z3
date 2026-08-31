/*++
Copyright (c) 2026 Microsoft Corporation

Tests for the sequence power operator s^n:
rewrite rules and the axioms used by the sequence solver.

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/seq_decl_plugin.h"
#include "smt/smt_context.h"

static void tst_power_rewriter() {
    ast_manager m;
    reg_decl_plugins(m);
    th_rewriter rw(m);
    seq_util seq(m);
    arith_util a(m);

    sort* str_sort = seq.str.mk_string_sort();
    app_ref x(m.mk_const("x", str_sort), m);
    app_ref n(m.mk_const("n", a.mk_int()), m);
    app_ref k(m.mk_const("k", a.mk_int()), m);
    expr_ref emp(seq.str.mk_empty(str_sort), m);

    auto power = [&](expr* s, expr* k) { return expr_ref(seq.str.mk_power(s, k), m); };
    auto powi = [&](expr* s, int k) { return power(s, a.mk_int(k)); };
    auto simp = [&](expr_ref e) { rw(e); return e; };

    ENSURE(simp(powi(x, 0)) == emp);
    ENSURE(simp(powi(x, -2)) == emp);
    ENSURE(simp(powi(x, 1)) == x);
    ENSURE(simp(power(emp, n)) == emp);

    // a constant base folds into a string
    ENSURE(simp(powi(seq.str.mk_string(zstring("ab")), 2)) == seq.str.mk_string(zstring("abab")));

    // a small exponent unfolds into a concatenation
    ENSURE(simp(powi(x, 2)) == seq.str.mk_concat(x, x));

    // exponents beyond rewriter.max_power_expansion are left alone
    ENSURE(seq.str.is_power(simp(powi(x, 3))));
    ENSURE(seq.str.is_power(simp(powi(seq.str.mk_string(zstring("ab")), 3))));
    params_ref p;
    p.set_uint("max_power_expansion", 4);
    th_rewriter rw4(m, p);
    expr_ref x3(powi(x, 3));
    rw4(x3);
    ENSURE(x3 == seq.str.mk_concat(x, seq.str.mk_concat(x, x)));

    // (x^k)^l = x^(k*l)
    ENSURE(simp(power(powi(x, 100), a.mk_int(3))) == simp(powi(x, 300)));
    ENSURE(simp(power(power(x, n), a.mk_int(3))) == simp(power(x, a.mk_mul(a.mk_int(3), n))));

    // the length of an unexpanded power is still known
    expr_ref big = simp(powi(x, 1000));
    ENSURE(simp(expr_ref(seq.str.mk_length(big), m)) ==
           simp(expr_ref(a.mk_mul(a.mk_int(1000), seq.str.mk_length(x)), m)));

    // symbolic exponents are not touched
    ENSURE(seq.str.is_power(simp(power(x, n))));

    // equality rewrites for powers
    ENSURE(simp(expr_ref(m.mk_eq(power(x, n), emp), m)) ==
           simp(expr_ref(m.mk_or(a.mk_le(n, a.mk_int(0)), m.mk_eq(x, emp)), m)));
    ENSURE(simp(expr_ref(m.mk_eq(power(x, n), power(x, k)), m)) ==
           simp(expr_ref(m.mk_or(m.mk_eq(x, emp),
                                 m.mk_and(a.mk_le(n, a.mk_int(0)), a.mk_le(k, a.mk_int(0))),
                                 m.mk_and(a.mk_lt(a.mk_int(0), n), a.mk_lt(a.mk_int(0), k), m.mk_eq(n, k))), m)));
}

static lbool check(ast_manager& m, expr_ref_vector const& fmls) {
    smt_params sp;
    smt::context ctx(m, sp);
    for (expr* f : fmls)
        ctx.assert_expr(f);
    return ctx.check();
}

static void tst_power_solver() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    arith_util a(m);

    sort* str_sort = seq.str.mk_string_sort();
    app_ref x(m.mk_const("x", str_sort), m);
    app_ref n(m.mk_const("n", a.mk_int()), m);
    expr_ref ab(seq.str.mk_string(zstring("ab")), m);
    expr_ref_vector fmls(m);

    // "ab"^n = "abab" has the solution n = 2
    fmls.push_back(m.mk_eq(seq.str.mk_power(ab, n), seq.str.mk_string(zstring("abab"))));
    ENSURE(check(m, fmls) == l_true);

    // the length of "ab"^n is even
    fmls.reset();
    fmls.push_back(m.mk_eq(seq.str.mk_power(ab, n), seq.str.mk_string(zstring("aba"))));
    ENSURE(check(m, fmls) == l_false);

    // x^n is empty for n <= 0
    fmls.reset();
    fmls.push_back(a.mk_le(n, a.mk_int(0)));
    fmls.push_back(m.mk_eq(seq.str.mk_power(x, n), seq.str.mk_string(zstring("a"))));
    ENSURE(check(m, fmls) == l_false);

    // x^n = "aaaa" with |x| = 2 has the solution x = "aa", n = 2
    fmls.reset();
    fmls.push_back(m.mk_eq(seq.str.mk_power(x, n), seq.str.mk_string(zstring("aaaa"))));
    fmls.push_back(m.mk_eq(seq.str.mk_length(x), a.mk_int(2)));
    ENSURE(check(m, fmls) == l_true);

    // the unfolding is exact for a fixed exponent
    fmls.reset();
    fmls.push_back(a.mk_eq(n, a.mk_int(3)));
    fmls.push_back(m.mk_not(m.mk_eq(seq.str.mk_power(x, n), seq.str.mk_concat(x, seq.str.mk_concat(x, x)))));
    ENSURE(check(m, fmls) == l_false);
}

void tst_seq_power() {
    tst_power_rewriter();
    tst_power_solver();
}
