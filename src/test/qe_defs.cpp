#include "arith_decl_plugin.h"
#include "qe.h"
#include "ast_pp.h"
#include "smtparser.h"
#include "reg_decl_plugins.h"


static void test_defs(ast_manager& m, expr* _fml) {
    arith_util a(m);
    app_ref x(m);
    qe::def_vector defs(m);
    expr_ref fml(_fml, m);
    x = m.mk_const(symbol("x"), a.mk_int());
    app* vars[1] = { x.get() };
    front_end_params fparams;
    qe::expr_quant_elim qelim(m, fparams);
    lbool result = qelim.first_elim(1, vars, fml, defs);
    std::cout << mk_pp(_fml, m) << "\n--->\n";
    std::cout << mk_pp(fml, m)  << "\n";
    for (unsigned i = 0; i < defs.size(); ++i) {
        std::cout << defs.var(i)->get_name() << " " 
                  << mk_pp(defs.def(i), m) << "\n";
    }
    std::cout << "\n";
}

static void test_defs_all(ast_manager& m, expr* _fml) {
    arith_util a(m);
    app_ref x(m);
    expr_ref fml(_fml, m), fml0(_fml, m);
    x = m.mk_const(symbol("x"), a.mk_int());
    app* vars[1] = { x.get() };
    front_end_params fparams;
    qe::expr_quant_elim qelim(m, fparams);
    lbool result = l_true;
    while (result == l_true) {
        fml = fml0;
        qe::def_vector defs(m);
        result = qelim.first_elim(1, vars, fml, defs);
        std::cout << result << "\n";
        std::cout << mk_pp(fml, m) << "\n";
        for (unsigned i = 0; i < defs.size(); ++i) {
            std::cout << defs.var(i)->get_name() << " " 
                      << mk_pp(defs.def(i), m) << "\n";
        }
        fml0 = m.mk_and(fml0, m.mk_not(fml));
    }
}

static void test_defs(char const* str) {
    ast_manager m;
    reg_decl_plugins(m);    
    scoped_ptr<smtlib::parser> parser = smtlib::parser::create(m);
    parser->initialize_smtlib();
    std::ostringstream buffer;
    buffer << "(benchmark presburger :status unknown :logic AUFLIA "
           << ":extrafuns ((x Int) (y Int) (z Int))\n"
           << ":formula " << str << ")";
    parser->parse_string(buffer.str().c_str());
    smtlib::benchmark* b = parser->get_benchmark();
    smtlib::theory::expr_iterator it  = b->begin_formulas();
    smtlib::theory::expr_iterator end = b->end_formulas();
    for (; it != end; ++it) {
        test_defs(m, *it);
    }
}

void tst_qe_defs() {
    enable_trace("qe");
    test_defs("(and (<= (* 2 x) y) (>= (* 3 x) z) (<= (* 4 x) (* 2 z)) (= (mod x 2) 0))");

    return;
    test_defs("(and (<= (* 2 x) y) (>= (* 3 x) z) (= (mod x 2) 0))");
    test_defs("(and (<= (* 2 x) y) (= (mod x 2) 0))");
    test_defs("(= (* 2 x) y)");
    test_defs("(or (< x 0) (> x 1))");
    test_defs("(or (< x y) (> x y))");
    test_defs("(= x y)");
    test_defs("(<= x y)");
    test_defs("(>= x y)");
    test_defs("(and (<= (+ x y) 0) (<= (+ x z) 0))");
    test_defs("(and (<= (+ x y) 0) (<= (+ (* 2 x) z) 0))");
    test_defs("(and (<= (+ (* 3 x) y) 0) (<= (+ (* 2 x) z) 0))");
    test_defs("(and (>= x y) (>= x z))");
    test_defs("(< x y)");
    test_defs("(> x y)");
}
