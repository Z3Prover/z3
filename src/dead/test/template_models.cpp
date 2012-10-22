#include "ast_fm.h"
#include "smtparser.h"
#include "ast_pp.h"

static void
simplify_formula(
    ast_manager&      ast_manager,
    smtlib::symtable* table,
    smtlib::parser*   parser,
    ast*              formula
    )
{
//     front_end_params params;
//     std::cout << std::make_pair(&ast_manager, formula) << std::endl;

//     const_decl_ast *le_decl = 0, *add_decl = 0, *mul_decl = 0; 
//     const_decl_ast *lt_decl = 0, *gt_decl = 0, *f_decl = 0;
//     type_decl_ast*  int_decl = 0;
//     type_ast* int_type = 0;

//     table->find1("<=", le_decl);
//     table->find1("+", add_decl);
//     table->find1("*", mul_decl);
//     table->find1("f", f_decl);
//     table->find1("<", lt_decl);
//     table->find1(">", gt_decl);
//     table->find("Int", int_decl);
//     int_type = ast_manager.mk_type(int_decl);
    

//     ast_simplifier simplifier(ast_manager, params);

// #if 0
//     iast_arith_simplifier* arith = 
//         simplifier.add_arithmetic(
// 			null_theory_id, // TBD
//             add_decl,
//             mul_decl,
//             le_decl,
//             false
//             );

//     arith->register_lt(lt_decl);
//     arith->register_gt(gt_decl);
// #endif
//     ast_fm fm(ast_manager, simplifier, le_decl, add_decl, mul_decl);

//     ast_function_replace replace(ast_manager);

//     ast_ref<> templ(ast_manager);
//     templ = ast_manager.mk_const(add_decl, 
// 		ast_manager.mk_var(0,int_type), 
// 		ast_manager.mk_numeral(rational(2), int_type));

//     ast_ref<> result(ast_manager);

//     //
//     // Replace f by \lambda x . x + 2 in formula.
//     //
    
//     replace(formula, f_decl, 1, templ.get(), result);

//     std::cout << "substituted:" 
//               << std::make_pair(&ast_manager, result.get()) << std::endl;
    
//     //
//     // Eliminate quantified variables from the formula.
//     //
//     fm.eliminate(result.get(), result);

//     std::cout << "projected:" 
//               << std::make_pair(&ast_manager, result.get()) << std::endl;

}

void tst_template_models()
{
    const char* spec = 
        "(benchmark template_models :logic QF_LIA \n"
        ":extrafuns ((f Int Int) (b Int) (c Int))\n"
        ":formula (forall (x Int) (and (< (f x) (f (+ x 1))) (> (f b) b) (> (f c) b))))";
    
    ast_manager ast_manager;
    smtlib::parser* parser = smtlib::parser::create(ast_manager);

    parser->initialize_smtlib();

    parser->parse_string(spec);

    smtlib::benchmark* b = parser->get_benchmark();
    
    smtlib::symtable* table = b->get_symtable();
    vector<smtlib::formula,false> formulas;
    b->get_formulas(formulas);
    for (unsigned j = 0; j < formulas.size(); ++j) {
        simplify_formula(ast_manager, table, 
                         parser, formulas[j].m_formula);
    }
    
    dealloc(parser);
}
