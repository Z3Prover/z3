
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "ast/rewriter/th_rewriter.h"
#include "parsers/smt2/smt2parser.h"
#include "ast/arith_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/ast_pp.h"


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
    ENSURE(ctx.begin_assertions() != ctx.end_assertions());
    result = *ctx.begin_assertions();
    return result;
}

static char const* example1 = "(= (+ (- (* x x) (* 2 y)) y) 0)";
static char const* example2 = "(= (+ 4 3 (- (* x x) (* 2 y)) y) 0)";


class poly_nf {
    expr_ref        m_coefficient;
    expr_ref_vector m_coefficients;
    expr_ref_vector m_factors;
public:
    poly_nf(ast_manager& m):
        m_coefficient(m),
        m_coefficients(m),
        m_factors(m) {}
    
    expr_ref& coefficient() { return m_coefficient; }
    expr_ref_vector& coefficients() { return m_coefficients; }
    expr_ref_vector& factors() { return m_factors; }

    void reset() {
        m_coefficient.reset();
        m_coefficients.reset();
        m_factors.reset();
    }

};

class polynorm {
    ast_manager&   m;
    arith_util     m_arith;
    arith_rewriter m_arith_rw;
    th_rewriter    m_rw;
public:
    polynorm(ast_manager& m): m(m), m_arith(m), m_arith_rw(m), m_rw(m) {}

private:
    expr_ref_vector mk_fresh_constants(unsigned num, sort* s) {
        expr_ref_vector result(m);
        for (unsigned i = 0; i < num; ++i) {
            result.push_back(m.mk_fresh_const("fresh", s));
        }
        return result;
    }

    expr_ref_vector mk_fresh_reals(unsigned num) {
        return mk_fresh_constants(num, m_arith.mk_real());
    }

    expr_ref mk_mul(unsigned num_args, expr* const* args) {
        expr_ref result(m);
        m_arith_rw.mk_mul(num_args, args, result);
        return result;
    }

    void nf(expr_ref& term, obj_hashtable<expr>& constants, poly_nf& poly) {

        expr_ref_vector& factors = poly.factors();
        expr_ref_vector& coefficients = poly.coefficients();
        expr_ref& coefficient = poly.coefficient();
        (void) coefficient;
        (void) coefficients;

        m_rw(term);

        if (m_arith.is_add(term)) {
            factors.append(to_app(term)->get_num_args(), to_app(term)->get_args());
        }
        else {
            factors.push_back(term);
        }
        for (unsigned i = 0; i < factors.size(); ++i) {
            expr* f = factors[i].get();
            unsigned num_args = 1;
            expr* const* args = &f;
            if (m_arith.is_mul(f)) {
                num_args = to_app(f)->get_num_args();
                args = to_app(f)->get_args();
            }
            for (unsigned j = 0; j < num_args; ++j) {
                if (m_arith.is_numeral(args[j]) || constants.contains(args[j])) {
                    //consts.push_back(args[j]);
                }
                else {
                    // vars.push_back(args[j]);
                }
                // deal with the relevant corner cases.
            }
#if 0
            rational r;
            if (m_arith.is_mul(f) && m_arith.is_numeral(to_app(f)->get_arg(0), r)) {
                coefficients.push_back(r);            
                factors[i] = mk_mul(to_app(f)->get_num_args()-1, to_app(f)->get_args()+1);
            }
            else if (m_arith.is_numeral(f, r)) {
                factors[i] = factors.back();
                factors.pop_back();
                ENSURE(coefficient.is_zero());
                ENSURE(!r.is_zero());
                coefficient = r;
                --i; // repeat examining 'i'
            }
            else {
                coefficients.push_back(rational(1));
            }
#endif
        }

        TRACE("polynorm",
              tout << mk_pp(coefficient, m) << "\n";
              for (unsigned i = 0; i < factors.size(); ++i) {
                  tout << mk_pp(factors[i].get(), m) << " * " << mk_pp(coefficients[i].get(), m) << "\n";
              });
    }
};

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
    expr *e1 = nullptr, *e2 = nullptr;

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
            ENSURE(coefficient.is_zero());
            ENSURE(!r.is_zero());
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
