/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/rewriter/arith_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/proofs/proof_checker.h"
#include "model/model.h"
#include "ast/rewriter/arith_swine.h"
#include "parsers/smt2/smt2parser.h"
#include <iostream>

static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Real)\n"
           << "(declare-const y Real)\n"
           << "(declare-const z Real)\n"
           << "(declare-const a Real)\n"
           << "(declare-const b Real)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    ENSURE(!ctx.assertions().empty());
    result = ctx.assertions().get(0);
    return result;
}

static char const* example1 = "(<= (+ (* 1.3 x y) (* 2.3 y y) (* (- 1.1 x x))) 2.2)";
static char const* example2 = "(= (+ 4 3 (- (* 3 x x) (* 5 y)) y) 0)";

static expr_ref parse_int_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const I Int)\n"
           << "(declare-const S Int)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    ENSURE(!ctx.assertions().empty());
    result = ctx.assertions().get(0);
    return result;
}

static void check_integer_power_lemmas() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_int()), m), y(m.mk_const(symbol("y"), a.mk_int()), m);
    expr_ref z(m.mk_const(symbol("z"), a.mk_int()), m), w(m.mk_const(symbol("w"), a.mk_int()), m);
    expr_ref p(a.mk_power(x, y), m), q(a.mk_power(z, w), m);
    struct sample { int x, y, value, z, w, other; bool pair; };
    sample samples[] = {
        {-3, -2, 8, 0, 0, 0, false},
        {3, 4, 2, 2, 3, 8, true},
        {3, 4, 1, 0, 0, 0, false},
        {2, 3, 8, 2, 4, 17, true},
        {3, 9, 19684, 0, 0, 0, false},
        {3, 9, 19682, 0, 0, 0, false},
    };
    arith_swine swine(m);
    for (auto const& s : samples) {
        vector<arith_swine::power> powers;
        powers.push_back({p, x, y, rational(s.x), rational(s.y), rational(s.value)});
        if (s.pair)
            powers.push_back({q, z, w, rational(s.z), rational(s.w), rational(s.other)});
        expr_ref_vector lemmas(m);
        auto value = [&](expr* e, rational& r) { return a.is_numeral(e, r); };
        ENSURE(swine.check(powers, value, lemmas) == l_false);
        for (int base : {-3, 0, 1, 2, 3, 4, 7}) {
            for (int exponent : {-3, 0, 1, 2, 4, 8, 9, 10}) {
                for (int other_base : {0, 2, 3, 7}) {
                    for (int other_exponent : {0, 1, 3, 4, 10}) {
                        model mdl(m);
                        expr_ref xv(a.mk_int(base), m), yv(a.mk_int(exponent), m);
                        expr_ref zv(a.mk_int(other_base), m), wv(a.mk_int(other_exponent), m);
                        mdl.register_decl(to_app(x)->get_decl(), xv);
                        mdl.register_decl(to_app(y)->get_decl(), yv);
                        mdl.register_decl(to_app(z)->get_decl(), zv);
                        mdl.register_decl(to_app(w)->get_decl(), wv);
                        for (expr* lemma : lemmas) {
                            expr_ref result(m);
                            ENSURE(mdl.eval_expr(lemma, result));
                            ENSURE(m.is_true(result));
                        }
                    }
                }
            }
        }
    }
}

static void tst_proof_associative_flattening() {
    for (bool conjunction : {false, true}) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        expr_ref_vector args(m);
        expr_ref input(m);
        for (unsigned i = 0; i < 512; ++i) {
            args.push_back(m.mk_const(symbol(i), m.mk_bool_sort()));
            if (i == 0)
                input = args.get(0);
            else
                input = conjunction ? m.mk_and(input, args.get(i)) : m.mk_or(input, args.get(i));
        }
        th_rewriter rw(m);
        expr_ref result(m);
        proof_ref proof(m);
        rw(input, result, proof);
        expr_ref expected(conjunction ? m.mk_and(args) : m.mk_or(args), m);
        ENSURE(result == expected && rw.get_num_steps() < 10);
        ENSURE(proof && m.get_fact(proof) == m.mk_eq(input, result));
        proof_checker checker(m);
        expr_ref_vector side_conditions(m);
        ENSURE(checker.check(proof, side_conditions));
    }
}

static void test_complex_logic_names() {
    for (symbol logic : {symbol::null, symbol("ALL"), symbol("QF_UF"),
                         symbol("QF_LRA"), symbol("QF_NRA"), symbol("QF_NTA"),
                         symbol("QF_UFLRA")}) {
        cmd_context ctx(false, nullptr, logic);
        ctx.init_manager();
        bool enabled = logic == symbol::null || logic == "ALL";
        ENSURE(ctx.is_sort_decl(symbol("Complex")) == enabled);
        for (char const* name : {"complex.make", "complex.real", "complex.imag"})
            ENSURE(ctx.is_func_decl(symbol(name)) == enabled);
        for (char const* name : {"complex", "real", "imag"})
            ENSURE(!ctx.is_func_decl(symbol(name)));
    }
}

static void tst_modular_inverse() {
    ast_manager m;
    reg_decl_plugins(m);
    th_rewriter rw(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::istringstream declarations("(declare-const I Int)(declare-const S Int)(declare-const T Int)");
    VERIFY(parse_smt2_commands(ctx, declarations));
    auto parse = [&](char const* text) {
        std::istringstream input(std::string("(assert ") + text + ")");
        VERIFY(parse_smt2_commands(ctx, input));
        return expr_ref(ctx.assertions().back(), m);
    };
    // Issue #11360: invert a coefficient after multiplication has distributed.
    for (char const* input : {
            "(= (mod (* 8691641 (+ I (* 1000 S) (* 1000000 T))) 100000007) 1)",
            "(= (mod (+ (* 8691641 I) (* 8691641000 S)) 100000007) 1)",
            "(= (mod (+ 3 (* 8691641 I) (* 8691641000 S)) 100000007) 4)",
            "(= 1 (mod (* 8691641 (+ I (* 1000 S))) 100000007))" }) {
        expr_ref fml = parse(input);
        rw(fml);
        char const* expected_text = std::string(input).find("1000000 T") != std::string::npos ?
            "(= (mod (+ I (* 1000 S) (* 1000000 T)) 100000007) 31337042)" :
            "(= (mod (+ I (* 1000 S)) 100000007) 31337042)";
        expr_ref expected = parse(expected_text);
        rw(expected);
        ENSURE(fml == expected);
    }

    arith_util a(m);
    expr_ref i(m.mk_const(ctx.find_func_decl(symbol("I"))), m);
    expr_ref s(m.mk_const(ctx.find_func_decl(symbol("S"))), m);
    for (char const* input : {
            "(= (mod (* 3 I) 7) 2)",
            "(= 2 (mod (* 3 I) 7))",
            "(= (mod (+ (* 2 I) (* 2 S)) 5) 1)",
            "(= (mod (+ (* 3 I) (* 6 S)) 7) 2)",
            "(= (mod (+ 2 (* (- 3) I) (* 6 S)) 7) 0)",
            "(= (mod (+ (* 3 I S) (* 6 I)) 7) 2)",
            "(= (mod (+ (* 5 I) (* 10 S)) 12) 11)",
            "(= (mod (+ (* 2 I) (* 4 S)) 6) 1)",
            "(= (mod (+ (* 3 I) (* 6 S)) (- 7)) 2)",
            "(= (mod (+ (* 3 I) (* 6 S)) 0) 2)" }) {
        expr_ref original = parse(input);
        expr_ref rewritten(original, m);
        rw(rewritten);
        expr_ref again(rewritten, m);
        rw(again);
        ENSURE(again == rewritten);
        for (int x = -12; x <= 12; ++x) {
            for (int y = -12; y <= 12; ++y) {
                expr_safe_replace subst(m);
                subst.insert(i, a.mk_int(x));
                subst.insert(s, a.mk_int(y));
                expr_ref eq(m.mk_eq(original, rewritten), m);
                subst(eq);
                rw(eq);
                ENSURE(m.is_true(eq));
            }
        }
    }
}

static void tst_inverse_trig_domains() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    arith_rewriter ar(m);
    th_rewriter rw(m);
    struct {
        decl_kind outer, inner;
    } const compositions[] = {
        {OP_SIN, OP_ASIN}, {OP_COS, OP_ACOS}, {OP_SIN, OP_ACOS},
        {OP_COSH, OP_ACOSH}, {OP_TANH, OP_ATANH}
    };
    for (auto const& c : compositions) {
        for (rational const& k : {rational(-2), rational(-1), rational(-3, 4), rational(0),
                                  rational(3, 4), rational(1), rational(2)}) {
            expr_ref x(a.mk_numeral(k, false), m);
            expr_ref inverse(m.mk_app(a.get_family_id(), c.inner, x.get()), m);
            expr_ref term(m.mk_app(a.get_family_id(), c.outer, inverse.get()), m);
            expr_ref result(m);
            bool in_domain = c.inner == OP_ACOSH ? k >= rational(1) :
                c.inner == OP_ATANH ? k > rational(-1) && k < rational(1) :
                k >= rational(-1) && k <= rational(1);
            br_status status = ar.mk_app_core(to_app(term)->get_decl(), 1, to_app(term)->get_args(), result);
            ENSURE((status != BR_FAILED) == in_domain);
            if (in_domain) {
                expr_ref expected(x, m);
                if (c.outer == OP_SIN && c.inner == OP_ACOS) {
                    expected = a.mk_numeral(rational(1) - k * k, false);
                    expected = a.mk_power(expected, a.mk_numeral(rational(1, 2), false));
                }
                rw(expected);
                rw(result);
                expr_ref eq(m.mk_eq(result, expected), m);
                rw(eq);
                ENSURE(m.is_true(eq));
            }
            else {
                expr_ref diseq(m.mk_not(m.mk_eq(term, x)), m);
                rw(diseq);
                ENSURE(!m.is_false(diseq));
            }
        }
        expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
        expr_ref inverse(m.mk_app(a.get_family_id(), c.inner, x.get()), m);
        expr_ref term(m.mk_app(a.get_family_id(), c.outer, inverse.get()), m);
        expr_ref result(term, m);
        rw(result);
        ENSURE(result == term);
    }
}

void tst_arith_rewriter() {
    check_integer_power_lemmas();
    test_complex_logic_names();
    tst_proof_associative_flattening();
    tst_modular_inverse();
    tst_inverse_trig_domains();
    ast_manager m;
    reg_decl_plugins(m);
    arith_rewriter ar(m);
    arith_util au(m);
    expr_ref t1(m), t2(m), result(m);
    t1 = au.mk_numeral(rational(0),false);
    t2 = au.mk_numeral(rational(-3),false);
    expr* args[2] = { t1, t2 };
    ar.mk_mul(2, args, result);
    std::cout << mk_pp(result, m) << "\n";

    
    th_rewriter rw(m);
    {
        expr_ref i(m.mk_const(symbol("i"), au.mk_int()), m);
        expr_ref j(m.mk_const(symbol("j"), au.mk_int()), m);
        expr_ref k(m.mk_const(symbol("k"), au.mk_int()), m);
        expr_ref p(au.mk_power(i, j), m);
        ENSURE(au.is_int(p));
        expr_ref two(au.mk_int(2), m), minus_one(au.mk_int(-1), m), zero(au.mk_int(0), m);
        expr_ref square(au.mk_power(i, two), m), squared(au.mk_mul(i, i), m);
        rw(square);
        rw(squared);
        ENSURE(square == squared);
        expr_ref parity_power(au.mk_power(minus_one, j), m), zero_power(au.mk_power(zero, j), m);
        rw(parity_power);
        rw(zero_power);
        for (int exponent : {-4, -3, 0, 1, 2, 3}) {
            model mdl(m);
            expr_ref value(au.mk_int(exponent), m);
            mdl.register_decl(to_app(j)->get_decl(), value);
            expr_ref parity_value(m), zero_value(m);
            ENSURE(mdl.eval_expr(parity_power, parity_value));
            ENSURE(mdl.eval_expr(zero_power, zero_value));
            rational actual;
            ENSURE(au.is_numeral(parity_value, actual) && actual == (exponent % 2 == 0 ? 1 : -1));
            ENSURE(au.is_numeral(zero_value, actual) && actual == (exponent == 0 ? 1 : 0));
        }
        for (int base : {-3, -1, 0, 1, 2}) {
            for (int exponent : {-3, -1, 0, 1, 4}) {
                expr_ref b(au.mk_int(base), m), e(au.mk_int(exponent), m);
                expr_ref power_expr(au.mk_power(b, e), m);
                rw(power_expr);
                rational value;
                ENSURE(au.is_numeral(power_expr, value));
                ENSURE(value == power(rational(base), static_cast<unsigned>(exponent < 0 ? -exponent : exponent)));
                ENSURE(au.is_int(power_expr));
            }
        }
        expr_ref nested(au.mk_power(p, k), m);
        expr_ref product(au.mk_mul(j, k), m);
        expr_ref flattened(au.mk_power(i, product), m);
        rw(nested);
        rw(flattened);
        ENSURE(nested == flattened);

        expr_ref q(au.mk_power(k, j), m);
        expr_ref lhs(au.mk_mul(p, q), m);
        expr_ref bases(au.mk_mul(i, k), m);
        expr_ref rhs(au.mk_power(bases, j), m);
        rw(lhs);
        rw(rhs);
        ENSURE(lhs == rhs);

        expr_ref real_base(au.mk_real(2), m), real_exponent(au.mk_real(-3), m);
        expr_ref real_power(au.mk_power(real_base, real_exponent), m);
        rw(real_power);
        rational value;
        ENSURE(au.is_real(real_power) && au.is_numeral(real_power, value) && value == rational(1, 8));
    }
    {
        expr_ref one(au.mk_real(1), m), two(au.mk_real(2), m);
        expr_ref zero(au.mk_real(0), m), minus_one(au.mk_real(-1), m);
        expr_ref i(au.mk_complex(zero, one), m);
        expr_ref z(au.mk_complex(one, two), m);
        expr_ref square(au.mk_mul(i, i), m);
        rw(square);
        expr_ref expected(au.mk_complex(minus_one, zero), m);
        ENSURE(square == expected);
        expr_ref quotient(au.mk_div(z, z), m);
        rw(quotient);
        expected = au.mk_complex(one, zero);
        ENSURE(quotient == expected);
        expr_ref neg(au.mk_uminus(z), m);
        expr_ref sum(au.mk_add(z, neg), m);
        rw(sum);
        expected = au.mk_complex(zero, zero);
        ENSURE(sum == expected);
        expr_ref real(au.mk_real_part(z), m);
        expr_ref imag(au.mk_imag_part(z), m);
        rw(real);
        rw(imag);
        ENSURE(real == one && imag == two);
        expr_ref x(m.mk_const(symbol("complex-x"), au.mk_complex()), m);
        expr_ref eta(au.mk_real_part(x), m);
        expr_ref eta_im(au.mk_imag_part(x), m);
        expr_ref pair(au.mk_complex(eta, eta_im), m);
        expr_ref eq(m.mk_eq(x, pair), m);
        rw(eq);
        ENSURE(m.is_true(eq));
        ENSURE(au.is_complex(z) && !au.is_int_real(z));
        ENSURE(m.is_value(z));
        ENSURE(m.are_distinct(z, i));
        expr_ref scalar(m.mk_const(symbol("scalar"), au.mk_real()), m);
        expr_ref real_product(au.mk_mul(scalar, eta), m);
        expr_ref imag_product(au.mk_mul(scalar, eta_im), m);
        expected = au.mk_complex(real_product, imag_product);
        rw(expected);
        bool saved_coercions = m.int_real_coercions();
        for (bool coercions : {false, true}) {
            m.enable_int_real_coercions(coercions);
            for (bool scalar_first : {false, true}) {
                expr* args[] = { scalar_first ? scalar.get() : x.get(),
                                 scalar_first ? x.get() : scalar.get() };
                expr_ref product(au.mk_mul(args[0], args[1]), m);
                app* term = to_app(product);
                func_decl* decl = term->get_decl();
                ENSURE(decl->get_domain(0) == args[0]->get_sort());
                ENSURE(decl->get_domain(1) == args[1]->get_sort());
                ENSURE(decl->get_range() == au.mk_complex());
                ENSURE(!decl->is_associative() && !decl->is_commutative());
                ENSURE(term->get_arg(0) == args[0] && term->get_arg(1) == args[1]);
                sort* domain[] = { args[0]->get_sort(), args[1]->get_sort() };
                func_decl_ref from_sorts(m.mk_func_decl(au.get_family_id(), OP_MUL, 0, nullptr, 2, domain), m);
                ENSURE(from_sorts == decl);
                rw(product);
                ENSURE(product == expected);
            }
        }
        m.enable_int_real_coercions(saved_coercions);
    }
    expr_ref fml = parse_fml(m, example1);
    rw(fml);
    std::cout << mk_pp(fml, m) << "\n";


    fml = parse_fml(m, example2);
    rw(fml);
    std::cout << mk_pp(fml, m) << "\n";

    // Issue #7507: (>= (* I (+ I 1)) 0) should simplify to true
    fml = parse_int_fml(m, "(>= (* I (+ I 1)) 0)");
    rw(fml);
    std::cout << "consecutive product >= 0: " << mk_pp(fml, m) << "\n";
    ENSURE(m.is_true(fml));

    // (>= (* I (+ I (- 1))) 0) should also simplify to true (x*(x-1))
    fml = parse_int_fml(m, "(>= (* I (+ I (- 1))) 0)");
    rw(fml);
    std::cout << "consecutive product (minus) >= 0: " << mk_pp(fml, m) << "\n";
    ENSURE(m.is_true(fml));

    // Issue #7403: mod (a + y) y should simplify to mod a y for symbolic y
    // i.e. (= (mod (+ I S) S) (mod I S)) should reduce to true
    fml = parse_int_fml(m, "(= (mod (+ I S) S) (mod I S))");
    rw(fml);
    std::cout << "mod (a+y) y = mod a y: " << mk_pp(fml, m) << "\n";
    ENSURE(m.is_true(fml));

    // mod (a + 2*y) y should simplify to mod a y (multiple of modulus dropped)
    fml = parse_int_fml(m, "(= (mod (+ I (* 2 S)) S) (mod I S))");
    rw(fml);
    std::cout << "mod (a+2y) y = mod a y: " << mk_pp(fml, m) << "\n";
    ENSURE(m.is_true(fml));

    // mod (mod a b) b should simplify for non-zero numeral b
    fml = parse_int_fml(m, "(= (mod (mod I 3) 3) (mod I 3))");
    rw(fml);
    std::cout << "mod (mod a 3) 3 = mod a 3: " << mk_pp(fml, m) << "\n";
    ENSURE(m.is_true(fml));
}
