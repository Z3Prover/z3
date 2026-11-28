/*++
Copyright (c) 2026 Microsoft Corporation

Tests for the sequence power operator s^n:
rewrite rules and the axioms used by the sequence solver.

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_regex_witness.h"
#include "ast/seq_decl_plugin.h"
#include "model/model.h"
#include "model/model_evaluator.h"
#include "smt/smt_context.h"
#include "util/rlimit.h"
#include <string>

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
    {
        expr_ref x100 = powi(x, 100);
        expr_ref three(a.mk_int(3), m);
        expr_ref lhs = simp(power(x100, three));
        expr_ref rhs = simp(powi(x, 300));
        ENSURE(lhs == rhs);
    }
    {
        expr_ref xn = power(x, n);
        expr_ref three(a.mk_int(3), m);
        expr_ref lhs = simp(power(xn, three));
        expr_ref rhs = simp(power(x, a.mk_mul(three, n)));
        ENSURE(lhs == rhs);
    }

    // the length of an unexpanded power is still known
    expr_ref big = simp(powi(x, 1000));
    {
        expr_ref lhs = simp(expr_ref(seq.str.mk_length(big), m));
        expr_ref thousand(a.mk_int(1000), m);
        expr_ref len_x(seq.str.mk_length(x), m);
        expr_ref rhs = simp(expr_ref(a.mk_mul(thousand, len_x), m));
        ENSURE(lhs == rhs);
    }

    // symbolic exponents are not touched
    ENSURE(seq.str.is_power(simp(power(x, n))));

    // equality rewrites for powers
    {
        expr_ref lhs = simp(expr_ref(m.mk_eq(power(x, n), emp), m));
        expr_ref nonpositive(a.mk_le(n, a.mk_int(0)), m);
        expr_ref empty(m.mk_eq(x, emp), m);
        expr_ref rhs = simp(expr_ref(m.mk_or(nonpositive, empty), m));
        ENSURE(lhs == rhs);
    }
    {
        expr_ref xn = power(x, n);
        expr_ref xk = power(x, k);
        expr_ref lhs = simp(expr_ref(m.mk_eq(xn, xk), m));
        expr_ref empty(m.mk_eq(x, emp), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref n_nonpositive(a.mk_le(n, zero), m);
        expr_ref k_nonpositive(a.mk_le(k, zero), m);
        expr_ref both_nonpositive(m.mk_and(n_nonpositive, k_nonpositive), m);
        expr_ref n_positive(a.mk_lt(zero, n), m);
        expr_ref k_positive(a.mk_lt(zero, k), m);
        expr_ref equal(m.mk_eq(n, k), m);
        expr_ref positive_equal(m.mk_and(n_positive, k_positive, equal), m);
        expr_ref rhs = simp(expr_ref(m.mk_or(empty, both_nonpositive, positive_equal), m));
        ENSURE(lhs == rhs);
    }
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
    {
        expr_ref lhs(seq.str.mk_power(ab, n), m);
        expr_ref rhs(seq.str.mk_string(zstring("abab")), m);
        fmls.push_back(m.mk_eq(lhs, rhs));
    }
    ENSURE(check(m, fmls) == l_true);

    // the length of "ab"^n is even
    fmls.reset();
    {
        expr_ref lhs(seq.str.mk_power(ab, n), m);
        expr_ref rhs(seq.str.mk_string(zstring("aba")), m);
        fmls.push_back(m.mk_eq(lhs, rhs));
    }
    ENSURE(check(m, fmls) == l_false);

    // x^n is empty for n <= 0
    fmls.reset();
    fmls.push_back(a.mk_le(n, a.mk_int(0)));
    {
        expr_ref lhs(seq.str.mk_power(x, n), m);
        expr_ref rhs(seq.str.mk_string(zstring("a")), m);
        fmls.push_back(m.mk_eq(lhs, rhs));
    }
    ENSURE(check(m, fmls) == l_false);

    // x^n = "aaaa" with |x| = 2 has the solution x = "aa", n = 2
    fmls.reset();
    {
        expr_ref lhs(seq.str.mk_power(x, n), m);
        expr_ref rhs(seq.str.mk_string(zstring("aaaa")), m);
        fmls.push_back(m.mk_eq(lhs, rhs));
    }
    {
        expr_ref lhs(seq.str.mk_length(x), m);
        expr_ref rhs(a.mk_int(2), m);
        fmls.push_back(m.mk_eq(lhs, rhs));
    }
    ENSURE(check(m, fmls) == l_true);

    // the unfolding is exact for a fixed exponent
    fmls.reset();
    fmls.push_back(a.mk_eq(n, a.mk_int(3)));
    {
        expr_ref lhs(seq.str.mk_power(x, n), m);
        expr_ref rhs(seq.str.mk_concat(x, seq.str.mk_concat(x, x)), m);
        fmls.push_back(m.mk_not(m.mk_eq(lhs, rhs)));
    }
    ENSURE(check(m, fmls) == l_false);
}

static void tst_compact_power_values() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    seq_rewriter rw(m);
    th_rewriter normalize(m);
    expr_ref base(u.str.mk_string("ab"), m);
    rational count("1000000000000000000000000000000");
    expr_ref exponent(a.mk_int(count), m);
    expr_ref word(u.str.mk_power(base, exponent), m);
    rational length;
    ENSURE(rw.get_ground_seq_length(word, length) && length == count * rational(2));
    expr_ref part(m);
    ENSURE(rw.slice_ground_seq(word, length - rational(5), rational(4), part));
    normalize(part);
    ENSURE(part == u.str.mk_string("baba"));
    ENSURE(rw.slice_ground_seq(word, rational(-1), rational(1), part));
    ENSURE(u.str.is_empty(part));
    ENSURE(rw.slice_ground_seq(word, rational(0), length + rational(10), part) && part == word);
    ENSURE(rw.mk_seq_reverse(word, part));
    expr_ref ba(u.str.mk_string("ba"), m);
    expr_ref reversed(u.str.mk_power(ba, exponent), m);
    ENSURE(rw.compare_ground_seqs(part, reversed) == l_true);
    ENSURE(rw.compare_ground_seqs(word, reversed) == l_false);
    expr_ref twice(u.str.mk_string("abab"), m);
    expr_ref half(a.mk_int(count / rational(2)), m);
    expr_ref same(u.str.mk_power(twice, half), m);
    ENSURE(rw.compare_ground_seqs(word, same) == l_true);
    svector<unsigned> chars;
    for (unsigned i = 0; i < 5000; ++i) {
        chars.push_back('a');
        chars.push_back('b');
    }
    expr_ref literal(u.str.mk_string(zstring(chars.size(), chars.data())), m);
    expr_ref five_thousand(a.mk_int(5000), m);
    expr_ref moderate(u.str.mk_power(base, five_thousand), m);
    ENSURE(rw.compare_ground_seqs(moderate, literal) == l_true);

    model_ref md(alloc(model, m));
    expr_ref x(m.mk_const("compact", word->get_sort()), m);
    md->register_decl(to_app(x)->get_decl(), word);
    model_evaluator evaluate(*md);
    ENSURE(evaluate(x) == word);
    expr_ref len(u.str.mk_length(x), m);
    ENSURE(evaluate(len) == a.mk_int(length));
    expr_ref offset(a.mk_int(length - rational(5)), m);
    expr_ref four(a.mk_int(4), m);
    expr_ref extract(u.str.mk_substr(x, offset, four), m);
    ENSURE(evaluate(extract) == u.str.mk_string("baba"));
    expr_ref at(u.str.mk_at(x, offset), m);
    ENSURE(evaluate(at) == u.str.mk_string("b"));
    expr_ref equality(m.mk_eq(x, same), m);
    ENSURE(m.is_true(evaluate(equality)));
    equality = m.mk_eq(x, reversed);
    ENSURE(m.is_false(evaluate(equality)));

    expr_ref re(u.re.mk_to_re(base), m);
    expr_ref repeated(u.re.mk_star(re), m);
    expr_ref membership(u.re.mk_in_re(x, repeated), m);
    ENSURE(m.is_true(evaluate(membership)));
    repeated = u.re.mk_complement(repeated);
    membership = u.re.mk_in_re(x, repeated);
    ENSURE(m.is_false(evaluate(membership)));

    expr_ref integer(a.mk_int(7), m);
    expr_ref unit(u.str.mk_unit(integer), m);
    expr_ref sequence(u.str.mk_power(unit, exponent), m);
    ENSURE(rw.get_ground_seq_length(sequence, length) && length == count);
    ENSURE(rw.slice_ground_seq(sequence, length - rational(1), rational(1), part));
    ENSURE(part == unit);
    expr_ref zero(a.mk_int(0), m), negative(a.mk_int(-5), m);
    expr_ref empty(u.str.mk_power(base, negative), m);
    ENSURE(rw.get_ground_seq_length(empty, length) && length.is_zero());
    empty = u.str.mk_power(base, zero);
    ENSURE(rw.get_ground_seq_length(empty, length) && length.is_zero());
}

static void tst_compact_nseq_models() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    seq_rewriter rw(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    expr_ref x(m.mk_const("compact-witness", u.str.mk_string_sort()), m);
    expr_ref a_word(u.str.mk_string("a"), m);
    expr_ref b_word(u.str.mk_string("b"), m);
    expr_ref a_re(u.re.mk_to_re(a_word), m);
    expr_ref b_re(u.re.mk_to_re(b_word), m);
    b_re = u.re.mk_star(b_re);
    expr_ref body(u.re.mk_concat(a_re, b_re), m);
    for (unsigned count : {5u, 5000u, 1000000000u}) {
        smt::context ctx(m, params);
        expr_ref regex(u.re.mk_loop_proper(body, count, count), m);
        expr_ref membership(u.re.mk_in_re(x, regex), m);
        ctx.assert_expr(membership);
        ENSURE(ctx.check() == l_true);
        model_ref md;
        ctx.get_model(md);
        model_evaluator evaluate(*md);
        expr_ref word = evaluate(x);
        rational length;
        ENSURE(rw.get_ground_seq_length(word, length) && length == rational(count));
        ENSURE(m.is_true(evaluate(membership)));
        if (count > 4096) {
            expr_ref exponent(a.mk_int(count), m);
            ENSURE(word == u.str.mk_power(a_word, exponent));
        }
    }
    expr_ref exponent(a.mk_int(rational("1000000000000000000000000000000")), m);
    expr_ref power(u.str.mk_power(a_word, exponent), m);
    smt::context ctx(m, params);
    expr_ref equality(m.mk_eq(x, power), m);
    ctx.assert_expr(equality);
    ENSURE(ctx.check() == l_true);
    model_ref md;
    ctx.get_model(md);
    model_evaluator evaluate(*md);
    ENSURE(evaluate(x) == power && m.is_true(evaluate(equality)));
}

static void tst_compact_regex_bounds() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    seq_rewriter rw(m);
    expr_ref letter(u.str.mk_string("a"), m);
    expr_ref body(u.re.mk_to_re(letter), m);
    expr_ref regex(u.re.mk_loop_proper(body, UINT_MAX, UINT_MAX), m);
    expr_ref exponent(a.mk_int(rational(UINT_MAX)), m);
    expr_ref word(u.str.mk_power(letter, exponent), m);
    expr_ref candidate(m);
    expr_ref all_char(u.re.mk_full_char(regex->get_sort()), m);
    expr_ref bounded(u.re.mk_loop_proper(all_char, 0, UINT_MAX), m);
    expr_ref larger(a.mk_int(rational(UINT_MAX) + rational(1)), m);
    expr_ref too_long(u.str.mk_power(letter, larger), m);
    for (auto mode : {seq::transition_mode::brzozowski_tm, seq::transition_mode::light_antimirov_tm}) {
        seq::regex_witness witness(rw, mode);
        ENSURE(witness.get_compact_witness(regex, candidate) == l_true && candidate == word);
        ENSURE(witness.accepts(candidate, regex) == l_true);
        ENSURE(witness.accepts(candidate, bounded) == l_true);
        ENSURE(witness.accepts(too_long, bounded) == l_false);
        expr_ref unbounded(u.re.mk_star(all_char), m);
        ENSURE(witness.accepts(too_long, unbounded) == l_true);
        expr_ref complement(u.re.mk_complement(regex), m);
        ENSURE(witness.accepts(candidate, complement) == l_false);
    }
}

static void tst_compact_model_dependencies() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    arith_util a(m);
    smt_params params;
    params.m_string_solver = symbol("nseq");
    expr_ref x(m.mk_const("power-result", u.str.mk_string_sort()), m);
    expr_ref y(m.mk_const("power-base", x->get_sort()), m);
    expr_ref count(a.mk_int(1000000000), m), two(a.mk_int(2), m);
    expr_ref power(u.str.mk_power(y, count), m);
    expr_ref equality(m.mk_eq(x, power), m);
    expr_ref length(u.str.mk_length(y), m);
    expr_ref length_eq(m.mk_eq(length, two), m);
    smt::context ctx(m, params);
    ctx.assert_expr(equality);
    ctx.assert_expr(length_eq);
    ENSURE(ctx.check() == l_true);
    model_ref md;
    ctx.get_model(md);
    model_evaluator evaluate(*md);
    ENSURE(m.is_true(evaluate(equality)) && m.is_true(evaluate(length_eq)));
    ENSURE(u.str.is_power(evaluate(x)));

    sort_ref seq_sort(u.str.mk_seq(m.mk_bool_sort()), m);
    expr_ref p(m.mk_const("fresh-p", seq_sort), m);
    expr_ref q(m.mk_const("fresh-q", seq_sort), m);
    expr_ref len_p(u.str.mk_length(p), m), len_q(u.str.mk_length(q), m);
    expr_ref p_length(m.mk_eq(len_p, count), m), q_length(m.mk_eq(len_q, count), m);
    expr_ref distinct(m.mk_not(m.mk_eq(p, q)), m);
    smt::context generic(m, params);
    generic.assert_expr(p_length);
    generic.assert_expr(q_length);
    generic.assert_expr(distinct);
    ENSURE(generic.check() == l_true);
    model_ref model;
    generic.get_model(model);
    model_evaluator eval_generic(*model);
    ENSURE(m.is_true(eval_generic(p_length)) && m.is_true(eval_generic(q_length)));
    ENSURE(m.is_true(eval_generic(distinct)));
}

// power_trichotomy (seq.power_trichotomy) and the fixes it depends on.
static void tst_power_trichotomy() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util seq(m);
    arith_util a(m);

    sort* str_sort = seq.str.mk_string_sort();
    app_ref x(m.mk_const("x", str_sort), m);
    app_ref y(m.mk_const("y", str_sort), m);
    app_ref w(m.mk_const("w", str_sort), m);
    app_ref r(m.mk_const("r", str_sort), m);
    app_ref mm(m.mk_const("m", a.mk_int()), m);
    app_ref n(m.mk_const("n", a.mk_int()), m);
    app_ref i(m.mk_const("i", a.mk_int()), m);
    app_ref j(m.mk_const("j", a.mk_int()), m);
    auto str = [&](char const* s) { return expr_ref(seq.str.mk_string(zstring(s)), m); };
    auto cat = [&](expr* s, expr* t) { return expr_ref(seq.str.mk_concat(s, t), m); };
    auto pw = [&](expr* s, expr* k) { return expr_ref(seq.str.mk_power(s, k), m); };
    expr_ref_vector fmls(m);

    // x^m . "b" . r = "ab"^n forces m = 1 (x = (ab)^q a); m >= 2 is unsat.
    // Plain power unfolding cannot refute this for all n.
    fmls.push_back(a.mk_ge(mm, a.mk_int(2)));
    fmls.push_back(m.mk_eq(cat(pw(x, mm), cat(str("b"), r)), pw(str("ab"), n)));
    ENSURE(check(m, fmls) == l_false);

    // x^m . r = y^n with xy != yx, m,n >= 2 is sat through form f3
    // (x = "aba", y = "abaab").
    fmls.reset();
    fmls.push_back(a.mk_ge(mm, a.mk_int(2)));
    fmls.push_back(a.mk_ge(n, a.mk_int(2)));
    fmls.push_back(a.mk_ge(seq.str.mk_length(x), a.mk_int(1)));
    fmls.push_back(m.mk_not(m.mk_eq(cat(x, y), cat(y, x))));
    fmls.push_back(m.mk_eq(cat(pw(x, mm), r), pw(y, n)));
    ENSURE(check(m, fmls) == l_true);

    // ... and with m >= 3 and |y| < 2|x| it is unsat: f3 needs (m-1)|x| < |y|.
    fmls.reset();
    fmls.push_back(a.mk_ge(mm, a.mk_int(3)));
    fmls.push_back(a.mk_ge(n, a.mk_int(1)));
    fmls.push_back(a.mk_ge(seq.str.mk_length(x), a.mk_int(1)));
    fmls.push_back(a.mk_lt(seq.str.mk_length(y), a.mk_mul(a.mk_int(2), seq.str.mk_length(x))));
    fmls.push_back(m.mk_not(m.mk_eq(cat(x, y), cat(y, x))));
    fmls.push_back(m.mk_eq(cat(pw(x, mm), r), pw(y, n)));
    ENSURE(check(m, fmls) == l_false);

    // power_var_decompose must not cut a variable base only at token
    // boundaries: w = "abaab", i = j = 1, y = "aba" is a solution.
    fmls.reset();
    fmls.push_back(m.mk_eq(pw(w, i), str("abaab")));
    fmls.push_back(m.mk_eq(pw(w, j), cat(y, str("ab"))));
    fmls.push_back(a.mk_ge(i, a.mk_int(1)));
    fmls.push_back(a.mk_ge(j, a.mk_int(1)));
    fmls.push_back(a.mk_ge(seq.str.mk_length(w), a.mk_int(1)));
    ENSURE(check(m, fmls) == l_true);

    // Nested bases: (a (ba)^i)^m = (aba)^n with m >= 2 is sat (i = 1, m = n).
    fmls.reset();
    fmls.push_back(a.mk_ge(mm, a.mk_int(2)));
    fmls.push_back(a.mk_ge(n, a.mk_int(1)));
    fmls.push_back(m.mk_eq(pw(cat(str("a"), pw(str("ba"), i)), mm), pw(str("aba"), n)));
    ENSURE(check(m, fmls) == l_true);

    // (a b^i c)^m = (a b^j d)^n with m, n >= 1 is unsat: c occurs only on the left.
    fmls.reset();
    fmls.push_back(a.mk_ge(mm, a.mk_int(1)));
    fmls.push_back(a.mk_ge(n, a.mk_int(1)));
    fmls.push_back(m.mk_eq(pw(cat(str("a"), cat(pw(str("b"), i), str("c"))), mm),
                           pw(cat(str("a"), cat(pw(str("b"), j), str("d"))), n)));
    ENSURE(check(m, fmls) == l_false);
}

static void tst_long_literal_regex_validation() {
    ast_manager m;
    reg_decl_plugins(m);
    seq_util u(m);
    expr_ref x(m.mk_fresh_const("long-literal", u.str.mk_string_sort()), m);
    expr_ref a(u.str.mk_string("a"), m), b(u.str.mk_string("b"), m);
    expr_ref ar(u.re.mk_to_re(a), m), br(u.re.mk_to_re(b), m);
    br = u.re.mk_star(br);
    expr_ref body(u.re.mk_concat(ar, br), m);
    expr_ref regex(u.re.mk_loop_proper(body, 8192, 8192), m);
    for (bool accepted : {false, true}) {
        std::string text(8192, accepted ? 'a' : 'b');
        expr_ref word(u.str.mk_string(text.c_str()), m);
        model_ref md = alloc(model, m);
        md->register_decl(to_app(x)->get_decl(), word);
        model_evaluator evaluate(*md);
        expr_ref membership(u.re.mk_in_re(x, regex), m);
        {
            scoped_rlimit limit(m.limit(), 50000);
            ENSURE(evaluate(membership) == m.mk_bool_val(accepted));
        }
        expr_ref complement(u.re.mk_complement(regex), m);
        membership = u.re.mk_in_re(x, complement);
        {
            scoped_rlimit limit(m.limit(), 50000);
            ENSURE(evaluate(membership) == m.mk_bool_val(!accepted));
        }
    }
}

void tst_seq_power() {
    tst_long_literal_regex_validation();
    tst_power_rewriter();
    tst_power_solver();
    tst_compact_power_values();
    tst_compact_nseq_models();
    tst_compact_regex_bounds();
    tst_compact_model_dependencies();
    tst_power_trichotomy();
}
