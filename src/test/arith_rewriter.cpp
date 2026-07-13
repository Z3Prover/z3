/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/rewriter/arith_rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/model.h"
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


void tst_arith_rewriter() {
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
