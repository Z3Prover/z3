#include "expr_pattern_match.h"
#include "smtparser.h"
#include "ast_pp.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "array_decl_plugin.h"
#include "reg_decl_plugins.h"

void tst_expr_pattern_match() {
    ast_manager manager;
    reg_decl_plugins(manager);

    expr_pattern_match apm(manager);

    apm.display(std::cout);
    
    const char* test_string = "(benchmark patterns :status unknown :logic ALL   \n"
        ":extrasorts (S)                                                        \n"
        ":extrafuns ((R S S bool))                                              \n"
        ":formula (forall (x S) (y S) (z S)                                     \n"
        "             (or (not (R x y)) (not (R y z)) (R x z))                  \n"
	"           ;    :pats { (R x y) (R y z) }                               \n"
        "               :weight { 2 }                               \n"
	" )\n"
        ")";
    smtlib::parser* parser = smtlib::parser::create(manager);
    parser->initialize_smtlib();
    std::cout << "parsing test string\n";
    if (!parser->parse_string(test_string)) {
        UNREACHABLE();
    }
    std::cout << "test string parsed\n";
    smtlib::benchmark* bench = parser->get_benchmark();

    for (unsigned i = 0; i < bench->get_num_formulas(); ++i) {
        expr* fml = bench->begin_formulas()[i];
        SASSERT(fml->get_kind() == AST_QUANTIFIER);
        quantifier* qf = to_quantifier(fml);
        app_ref_vector patterns(manager);
        unsigned weight = 0;
        if (apm.match_quantifier(qf, patterns, weight)) {
            std::cout << "Found pattern match\n";
            for (unsigned i = 0; i < patterns.size(); ++i) {
                ast_pp(std::cout, patterns[i].get(), manager) << "\n";
            }
            std::cout << "weight: " << weight << "\n";
        }
    }
    dealloc(parser);

}
