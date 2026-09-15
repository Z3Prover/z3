/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "api/z3.h"
#include "util/debug.h"
#include <iostream>
#include <string>

// A macro must not be created for a symbol that occurs in the body of a
// recursive definition: the bodies of recursive definitions are not asserted
// formulas, so they are not updated when the defining axiom is removed.
static void test_macro_in_recursive_definition() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* spec =
        "(set-option :auto_config false)\n"
        "(set-option :smt.macro_finder true)\n"
        "(declare-fun f (Int) Bool)\n"
        "(define-fun-rec g ((x Int)) Bool (ite (> x 0) (f (- x 1)) false))\n"
        "(assert (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x)))))\n"
        "(declare-const n Int)\n"
        "(declare-const m Int)\n"
        "(assert (= n (+ m 1)))\n"
        "(assert (<= m 0))\n"
        "(assert (f n))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

// Macros over symbols unrelated to recursive definitions are still created.
static void test_macro_unrelated_to_recursive_definition() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* spec =
        "(set-option :auto_config false)\n"
        "(set-option :smt.macro_finder true)\n"
        "(declare-fun f (Int) Bool)\n"
        "(define-fun-rec g ((x Int)) Bool (ite (> x 0) (g (- x 1)) false))\n"
        "(assert (forall ((x Int)) (! (= (f x) (> x 0)) :pattern ((f x)))))\n"
        "(assert (f 0))\n"
        "(check-sat)\n";

    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

void tst_macro_finder() {
    test_macro_in_recursive_definition();
    test_macro_unrelated_to_recursive_definition();
}
