#include "native.h"

#include <iostream>

int main() {
    custard_init_globals();
    if (!Z3CherryTests_run()) {
        std::cerr << "Cherry kernel acceptance/rejection regressions failed\n";
        return 1;
    }
    z3::config config;
    config.set("proof", true);
    z3::context context(config);
    z3::solver solver(context);
    auto falsehood = context.bool_val(false);
    auto truth = context.bool_val(true);
    solver.add(falsehood);
    if (solver.check() != z3::unsat)
        return 1;
    auto proof = solver.proof();
    checker::NativeSession session(context);
    for (auto assertion : {falsehood, truth}) {
        auto inputs = checker::list<Prims_list__ast_Cons_s>({assertion});
        auto document = Z3Cherry_marshal(inputs, proof);
        checker_drop_asts(inputs);
        for (bool sorted : {false, true}) {
            auto result = Z3Cherry_check(sorted, document);
            bool accepted = result.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT &&
                cherry_int_eq(result.val.Some, CHERRY_INT_SMALL(0));
            checker_drop_result(result);
            if (accepted != Z3_is_eq_ast(context, assertion, falsehood)) {
                checker_drop_marshaled(document);
                std::cerr << "Cherry native assertion/proof binding regression failed\n";
                return 1;
            }
        }
        checker_drop_marshaled(document);
    }
    std::cout << "Cherry kernel and native acceptance/rejection regressions passed\n";
    return 0;
}
