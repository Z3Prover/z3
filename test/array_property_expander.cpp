#include "array_property_expander.h"
#include "array_property_recognizer.h"
#include "smtparser.h"
#include "array_decl_plugin.h"
#include "ast_pp.h"
#include <sstream>

static void test_array_expand(ast_manager& m, expr* fml) {
    std::cout << mk_pp(fml, m) << "\n";
    expr_ref_vector result(m);
    array_property_expander exp(m);
    array_property_recognizer rec(m);
    exp(1, &fml, result);
    std::cout << mk_pp(result[0].get(), m) << "\n";
    std::cout << rec(1, &fml) << "\n";
}


static void parse_string(char const* fml) {
    ast_manager m;
    m.register_plugin(symbol("array"), alloc(array_decl_plugin)); 
    scoped_ptr<smtlib::parser> parser = smtlib::parser::create(m);
    parser->initialize_smtlib();

    std::ostringstream buffer;
    buffer << "(benchmark array :status unknown :logic AUFLIA \n"
           << ":extrafuns ((A (Array Int Int)) (B (Array Int Int)))\n"
           << ":extrafuns ((C (Array Int (Array Int Int))))\n"
           << ":extrafuns ((D (Array Int Bool Int)))\n"
           << ":extrafuns ((i Int) (j Int))\n"
           << ":extrafuns ((f Int Int))\n"
           << ":formula " << fml << ")";
    parser->parse_string(buffer.str().c_str());
    smtlib::benchmark* b = parser->get_benchmark();
    smtlib::theory::expr_iterator it  = b->begin_formulas();
    smtlib::theory::expr_iterator end = b->end_formulas();
    for (; it != end; ++it) {
        test_array_expand(m, *it);
    }
}


void tst_array_property_expander() {
    parse_string("(= A B)");
    parse_string("(= A (store B i 4))");
    parse_string("(= C (store C 0 (store (select C 0) i 1)))");
    parse_string("(exists (i Int) (= C (store C 0 (store (select C 0) i 1))))");
    parse_string("(forall (i Int) (b Bool) (= D (store D i b 4)))");
    parse_string("(= (const[Array] 3) A)");
    parse_string("(= (map[f] A) B)");

}

