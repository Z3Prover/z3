#include "expr_context_simplifier.h"
#include "smtparser.h"
#include "ast_pp.h"

static void simplify_formula(ast_manager& m, expr* e) {
    expr_ref result(m);
    expr_context_simplifier simp(m);

    simp(e, result);

    TRACE("expr_context_simplifier",
          tout 
          << mk_pp(e, m) << " |-> " 
          << mk_pp(result.get(), m) << "\n";);
    
}

void tst_expr_context_simplifier() {
    ast_manager m;
    
    smtlib::parser* parser = smtlib::parser::create(m);
    m.register_decl_plugins();

    parser->initialize_smtlib();

    parser->parse_string(
        "(benchmark samples :logic QF_LIA                         \n"
        " :extrafuns ((x Int) (y Int) (z Int) (u Int))            \n"
        " :formula (and (<= 1 x) (or (<= 1 x) (<= x y)))          \n"
        " :formula (and (<= 2 (ite (<= z 1) (ite (<= z 1) x y) (* 2 x))) (<= x y)) \n"
        ")"
        );

    smtlib::benchmark* b = parser->get_benchmark();

    smtlib::symtable const * table = b->get_symtable();

    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        simplify_formula(m, b->begin_formulas()[j]);
    }

    dealloc(parser);
}
