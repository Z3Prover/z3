#include "native.h"

#include <iostream>
#include <vector>

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
    {
        std::vector<Z3_ast> assertions(100000, falsehood);
        auto inputs = checker::list<Prims_list__ast_Cons_s>(assertions);
        auto document = Z3Cherry_marshal(inputs, proof);
        checker_drop_asts(inputs);
        bool complete = checker::length<Prims_list__expr_Cons_s>(
            reinterpret_cast<Z3ProofDocument_document_Mk_document_s const*>(document.document)->assertions) == assertions.size();
        checker_drop_marshaled(document);
        if (!complete) {
            std::cerr << "Cherry wide native assertion marshalling regression failed\n";
            return 1;
        }
    }
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
    // Native flattening of hand-built `ff-pac` DAGs, as in the OCaml bridge tests.
    auto parsed = context.parse_string(
        "(define-sort F () (_ FiniteField 7))(declare-const z F)(assert (= z (as ff3 F)))");
    auto premise = parsed[0];
    auto numeral = premise.arg(1);
    auto P = context.uninterpreted_sort("P");
    auto I = context.int_sort();
    auto input = context.function("ff-input", I, P);
    auto add = context.function("ff-add", P, P, P);
    auto mul = context.function("ff-mul", P, numeral.get_sort(), I, P);
    auto integral = context.function("ff-mul", P, I, I, P);
    auto other = context.function("ff-sub", P, P, P);
    auto pac = context.function("ff-pac", P, P, P, P);
    auto support = context.function("ff-support", I, P);
    auto flatten = [&](z3::expr root, z3::expr p) -> long {
        auto premises = context.function("ff-premises", p.get_sort(), P);
        auto view = checker::view_ff_pac(pac(premises(p), root, support(context.int_val(0))));
        long nodes = view.tag == FSTAR_PERVASIVES_NATIVE_SOME__FF_PAC_VIEW ?
            static_cast<long>(checker::length<Prims_list__ff_pac_node_Cons_s>(view.val.Some.pac_nodes)) : -1;
        checker_drop_ff_pac(view);
        return nodes;
    };
    auto leaf = input(context.int_val(0));
    auto shared = leaf;
    for (int i = 0; i < 60; ++i)
        shared = add(shared, shared);
    auto chain = input(context.int_val(1));
    for (int i = 0; i < 200000; ++i)
        chain = add(chain, leaf);
    bool flattened =
        flatten(mul(add(leaf, input(context.int_val(1))), numeral, context.int_val(2)), premise) == 4 &&
        flatten(shared, premise) == 61 && flatten(chain, premise) == -1 &&
        flatten(input(context.int_val(-1)), premise) == -1 &&
        flatten(input(context.int_val("4294967296")), premise) == -1 &&
        flatten(integral(leaf, context.int_val(3), context.int_val(0)), premise) == -1 &&
        flatten(other(leaf, leaf), premise) == -1 && flatten(leaf, numeral) == -1;
    if (!flattened) {
        std::cerr << "Cherry native finite-field certificate flattening regression failed\n";
        return 1;
    }
    std::cout << "Cherry kernel and native acceptance/rejection regressions passed\n";
    return 0;
}
