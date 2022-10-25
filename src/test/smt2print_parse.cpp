
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

// This is to test the print-parse facilities over the API
// for SMT-LIB2.

#include "api/z3.h"
#include <iostream>

void test_print(Z3_context ctx, Z3_ast_vector av) {
    Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
    Z3_ast* args = new Z3_ast[Z3_ast_vector_size(ctx, av)];
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, av); ++i) {
        args[i] = Z3_ast_vector_get(ctx, av, i);
    }
    Z3_ast a = Z3_mk_and(ctx, Z3_ast_vector_size(ctx, av), args);
    Z3_inc_ref(ctx, a);
    delete[] args;
    char const* spec1 = Z3_benchmark_to_smtlib_string(ctx, "test", nullptr, nullptr, nullptr, 0, nullptr, a);
    Z3_dec_ref(ctx, a);
    std::cout << "spec1: benchmark->string\n" << spec1 << "\n";

    std::cout << "attempting to parse spec1...\n";
    Z3_ast_vector b = 
        Z3_parse_smtlib2_string(ctx, 
                                spec1,
                                0,
                                nullptr,
                                nullptr,
                                0,
                                nullptr,
                                nullptr);
    std::cout << "parse successful, converting ast->string\n";
    Z3_ast_vector_inc_ref(ctx, b);
    char const* spec2 = Z3_ast_vector_to_string(ctx, b);
    std::cout << "spec2: string->ast->string\n" << spec2 << "\n";
    Z3_ast_vector_dec_ref(ctx, b);
}

void test_parseprint(char const* spec) {
    Z3_context ctx = Z3_mk_context(nullptr);
    std::cout << "spec:\n" << spec << "\n";

    Z3_ast_vector a = 
        Z3_parse_smtlib2_string(ctx, 
                                spec,
                                0,
                                nullptr,
                                nullptr,
                                0,
                                nullptr,
                                nullptr);
    
    std::cout << "done parsing\n";
    Z3_ast_vector_inc_ref(ctx, a);
    test_print(ctx, a);

    std::cout << "done printing\n";

    Z3_ast_vector_dec_ref(ctx, a);
    Z3_del_context(ctx);
}

void test_eval(Z3_context ctx, Z3_string spec, bool shouldFail) {
    std::cout << "spec:\n" << spec << "\n";

    Z3_string resp;
    bool failed = false;
    try {
        resp = Z3_eval_smtlib2_string(ctx, spec);
    }
    catch (std::runtime_error& e) {
        resp = e.what();
        failed = true;
    }

    std::cout << "response:\n" << resp << "\n";

    if (shouldFail != failed) {
        if (shouldFail)
            throw std::runtime_error("should have failed");
        else
            throw std::runtime_error("should have succeeded");
    }
}

void throwError(Z3_context c, Z3_error_code e) {
    throw std::runtime_error(Z3_get_error_msg(c, e));
}

void test_repeated_eval() {
    // Z3_eval_smtlib2_string reuses the parser and the scanner
    // when called repeteadly on the same context.
    //
    // These tests rehearse that earlier calls do not interfere
    // with the result of later calls if the SMT queries are independent.

    char const* spec1 =
        "(push)\n"
        "(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))\n"
        "(declare-const x Int)\n"
        "(declare-const l (list Int))\n"
        "(declare-fun f ((list Int)) Bool)\n"
        "(assert (f (cons x l)))\n"
        "(check-sat)\n"
        "(pop)\n";

    char const* spec2 =
        "(push)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const b (Array (Array Int Int) Bool))\n"
        "(assert (select b a))\n"
        "(assert (= b ((as const (Array (Array Int Int) Bool)) true)))\n"
        "(assert (= b (store b a true)))\n"
        "(declare-const b1 (Array Bool Bool))\n"
        "(declare-const b2 (Array Bool Bool))\n"
        "(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))\n"
        "(check-sat)\n"
        "(pop)\n";

    char const* spec3 =
        "(push)\n"
        "(declare-const a@ (Array Int Int))\n"
        "(declare-const b (Array (Array Int Int) Bool))\n"
        "(assert (select b a))\n"
        "(check-sat)\n"
        "(pop)\n";

    char const* spec4 =
        "(push)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const b# (Array (Array Int Int) Bool))\n"
        "(assert (select b a))\n"
        "(check-sat)\n"
        "(pop)\n";

    Z3_context ctx = Z3_mk_context(nullptr);
    Z3_set_error_handler(ctx, throwError);
    std::cout << "testing Z3_eval_smtlib2_string\n";

    test_eval(ctx, spec1, false);
    std::cout << "successful call after successful call\n";
    test_eval(ctx, spec2, false);
    std::cout << "failing call after successful call\n";
    test_eval(ctx, spec3, true);
    std::cout << "failing call after failing call\n";
    test_eval(ctx, spec4, true);
    std::cout << "successful call after failing call\n";
    test_eval(ctx, spec1, false);

    std::cout << "done evaluating\n";

    Z3_del_context(ctx);
}

void tst_smt2print_parse() {

    // test basic datatypes  
    char const* spec1 = 
        "(declare-datatypes (T) ((list (nil) (cons (car T) (cdr list)))))\n"
        "(declare-const x Int)\n"
        "(declare-const l (list Int))\n"
        "(declare-fun f ((list Int)) Bool)\n"
        "(assert (f (cons x l)))\n";

    test_parseprint(spec1);

    // test basic arrays
    char const* spec2 = 
        "(declare-const x Int)\n"
        "(declare-const a (Array Int Int))\n"
        "(declare-const b (Array (Array Int Int) Bool))\n"
        "(assert (select b a))\n"
        "(assert (= b ((as const (Array (Array Int Int) Bool)) true)))\n"
        "(assert (= b (store b a true)))\n"
        "(declare-const b1 (Array Bool Bool))\n"
        "(declare-const b2 (Array Bool Bool))\n"
        "(assert (= ((as const (Array Bool Bool)) false) ((_ map and) b1 b2)))\n";

    // TBD: const, map, store

    test_parseprint(spec2);

    // Test mutually recursive datatypes
    char const* spec3 = 
        "(declare-datatypes () ((list (nil) (cons (car tree) (cdr list))) (tree (leaf) (node (n list)))))\n"
        "(declare-const x tree)\n"
        "(declare-const l list)\n"
        "(declare-fun f (list) Bool)\n"
        "(assert (f (cons x l)))\n";

    test_parseprint(spec3);

    // Test arithmetic
    char const* spec4 = 
        "(declare-const x Real)\n"
        "(declare-const y Int)\n"
        "(assert (= x 0.0))\n"
        "(assert (= y 6))\n"
        "(assert (> (/ x 1.4) (to_real y)))";

    test_parseprint(spec4);

    // Test bit-vectors
    char const* spec5 = 
        "(declare-const x (_ BitVec 4))\n"
        "(declare-const y (_ BitVec 4))\n"
        "(assert (bvule x (bvmul y (concat ((_ extract 2 0) x) ((_ extract 3 3) #xf0)))))";

    test_parseprint(spec5);

    // Test strings
    char const* spec6 =
        "(assert (= \"abc\" \"abc\"))";

    test_parseprint(spec6);

    // Test ?

    test_repeated_eval();

}
