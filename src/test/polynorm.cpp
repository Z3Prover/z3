#include "th_rewriter.h"
#include "smt2parser.h"
#include "arith_decl_plugin.h"
#include "reg_decl_plugins.h"
#include "ast_pp.h"


static expr_ref parse_fml(ast_manager& m, char const* str) {
    expr_ref result(m);
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    std::ostringstream buffer;
    buffer << "(declare-const x Int)\n"
           << "(declare-const y Int)\n"
           << "(declare-const z Int)\n"
           << "(declare-const a Int)\n"
           << "(declare-const b Int)\n"
           << "(assert " << str << ")\n";
    std::istringstream is(buffer.str());
    VERIFY(parse_smt2_commands(ctx, is));
    SASSERT(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* example1 = "(= (+ (- (* x x) (* 2 y)) y) 0)";
static char const* example2 = "(= (+ 4 3 (- (* x x) (* 2 y)) y) 0)";


// ast
///  sort : ast
///  func_decl : ast
///  expr : ast
///    app : expr
///    quantifier : expr
///    var : expr
/// 

static expr_ref mk_mul(arith_util& arith, unsigned num_args, expr* const* args) {
    ast_manager& m = arith.get_manager();
    expr_ref result(m);
    switch (num_args) {
    case 0: 
        UNREACHABLE();
        break;
    case 1:
        result = args[0];
        break;
    default:
        result = arith.mk_mul(num_args, args);
        break;
    }
    return result;
}

static void nf(expr_ref& term) {
    ast_manager& m = term.get_manager();
    expr *e1, *e2;

    th_rewriter rw(m);
    arith_util arith(m);

    VERIFY(m.is_eq(term, e1, e2));
    term = e1;
    
    rw(term);

    std::cout << mk_pp(term, m) << "\n";
    std::cout << arith.is_add(term) << "\n";
    
    expr_ref_vector factors(m);
    vector<rational> coefficients;
    rational coefficient(0);

    if (arith.is_add(term)) {
        factors.append(to_app(term)->get_num_args(), to_app(term)->get_args());
    }
    else {
        factors.push_back(term);
    }
    for (unsigned i = 0; i < factors.size(); ++i) {
        expr* f = factors[i].get();
        rational r;
        if (arith.is_mul(f) && arith.is_numeral(to_app(f)->get_arg(0), r)) {
            coefficients.push_back(r);            
            factors[i] = mk_mul(arith, to_app(f)->get_num_args()-1, to_app(f)->get_args()+1);
        }
        else if (arith.is_numeral(f, r)) {
            factors[i] = factors.back();
            factors.pop_back();
            SASSERT(coefficient.is_zero());
            SASSERT(!r.is_zero());
            coefficient = r;
            --i; // repeat examining 'i'
        }
        else {
            coefficients.push_back(rational(1));
        }
    }

    std::cout << coefficient << "\n";
    for (unsigned i = 0; i < factors.size(); ++i) {
        std::cout << mk_pp(factors[i].get(), m) << " * " << coefficients[i] << "\n";
    }
}

void tst_polynorm() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref fml(m);

    fml = parse_fml(m, example1);
    std::cout << mk_pp(fml, m) << "\n";
    nf(fml);

    fml = parse_fml(m, example2);
    std::cout << mk_pp(fml, m) << "\n";
    nf(fml);

    
}
