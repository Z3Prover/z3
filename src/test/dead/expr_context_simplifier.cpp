#include "expr_context_simplifier.h"
#include "smtparser.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"

static void check_equiv(ast_manager& m, expr* e1, expr* e2) {
    front_end_params fp;
    smt::solver solver(m, fp);
    expr_ref equiv(m);
    equiv = m.mk_not(m.mk_eq(e1,e2));
    solver.assert_expr(equiv);
    lbool is_sat = solver.check();
    SASSERT(is_sat == l_false);
}

static void simplify_formula(ast_manager& m, expr* e) {
    expr_ref result(m);
    expr_context_simplifier simp(m);

    simp(e, result);

    TRACE("expr_context_simplifier",
          tout 
          << mk_pp(e, m) << "\n|->\n" 
          << mk_pp(result.get(), m) << "\n";);

    check_equiv(m, e, result);
    
}

void tst_expr_context_simplifier() {
    ast_manager m;
    
    smtlib::parser* parser = smtlib::parser::create(m);
    reg_decl_plugins(m);

    parser->initialize_smtlib();

    parser->parse_string(
        "(benchmark samples :logic QF_LIA                         \n"
        " :extrafuns ((x Int) (y Int) (z Int) (u Int))            \n"
        " :extrapreds ((p) (q) (r)) \n"
        " :formula (and (<= 1 x) (or (<= 1 x) (<= x y)))          \n"
        " :formula (and (<= 2 (ite (<= z 1) (ite (<= z 1) x y) (* 2 x))) (<= x y)) \n"
        " :formula (or (and (not p) q (or (not r) (and (or (not p) q) r)))\
                       (and (not p) q (or (and p (not q) r) (and (or (not p) q) (not r)))) \
                       (and (or (and p (not q)) (and p q))\
                            (or (and p q r) (and (or (not p) (not q)) (not r))))\
                       (and (not p) (not q) (or (and (not p) q r) (and (or p (not q)) (not r))))\
                       (and (not p) (not q) (or (not r) (and (or p (not q)) r))))\n"
        ")"
        );

    smtlib::benchmark* b = parser->get_benchmark();

    smtlib::symtable const * table = b->get_symtable();

    for (unsigned j = 0; j < b->get_num_formulas(); ++j) {
        simplify_formula(m, b->begin_formulas()[j]);
    }

    dealloc(parser);
}
