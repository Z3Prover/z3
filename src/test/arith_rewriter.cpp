#include "arith_rewriter.h"
#include "bv_decl_plugin.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"
#include "th_rewriter.h"
#include "model.h"
#include "pdr_util.h"
#include "smt2parser.h"


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
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* example1 = "(<= (+ (* 1.3 x y) (* 2.3 y y) (* (- 1.1 x x))) 2.2)";
static char const* example2 = "(= (+ 4 3 (- (* 3 x x) (* 5 y)) y) 0)";


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
    pdr::normalize_arithmetic(fml);
    std::cout << mk_pp(fml, m) << "\n";


    fml = parse_fml(m, example2);
    rw(fml);
    std::cout << mk_pp(fml, m) << "\n";
    pdr::normalize_arithmetic(fml);
    std::cout << mk_pp(fml, m) << "\n";
}
