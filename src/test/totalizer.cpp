#include "opt/totalizer.h"
#include "ast/ast_pp.h"
#include "ast/reg_decl_plugins.h"
#include <iostream>

void tst_totalizer() {
    std::cout << "totalizer\n";
    ast_manager m;
    reg_decl_plugins(m);
    expr_ref_vector lits(m);
    for (unsigned i = 0; i < 5; ++i)
        lits.push_back(m.mk_fresh_const("a", m.mk_bool_sort()));
    opt::totalizer tot(lits);

    for (unsigned i = 0; i <= 6; ++i) {
        std::cout << "at least " << i << " ";
        expr* am = tot.at_least(i);
        std::cout << mk_pp(am, m) << "\n";        
    }
    for (auto& clause : tot.clauses()) 
        std::cout << clause << "\n";
}
