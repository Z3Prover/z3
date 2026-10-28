/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    parametric_datatype.cpp

Abstract:

    Test parametric datatypes with type variables.

Author:

    Copilot 2025-10-12

--*/

#include "api/z3.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "smt/smt_context.h"
#include "util/util.h"
#include <iostream>
#include <sstream>
#include <string>


/**
 * Test Z3_mk_polymorphic_datatype API with explicit parameters.
 * 
 * This test demonstrates the API that explicitly accepts type parameters.
 */
static void test_polymorphic_datatype_api() {
    std::cout << "test_polymorphic_datatype_api\n";
    
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    // Create type variables alpha and beta for polymorphic datatype
    Z3_symbol alpha_sym = Z3_mk_string_symbol(ctx, "alpha");
    Z3_symbol beta_sym = Z3_mk_string_symbol(ctx, "beta");
    Z3_sort alpha = Z3_mk_type_variable(ctx, alpha_sym);
    Z3_sort beta = Z3_mk_type_variable(ctx, beta_sym);
    
    // Define parametric triple datatype with constructor mk-triple(first: alpha, second: beta, third: alpha)
    Z3_symbol triple_name = Z3_mk_string_symbol(ctx, "triple");
    Z3_symbol mk_triple_name = Z3_mk_string_symbol(ctx, "mk-triple");
    Z3_symbol is_triple_name = Z3_mk_string_symbol(ctx, "is-triple");
    Z3_symbol first_name = Z3_mk_string_symbol(ctx, "first");
    Z3_symbol second_name = Z3_mk_string_symbol(ctx, "second");
    Z3_symbol third_name = Z3_mk_string_symbol(ctx, "third");
    
    Z3_symbol field_names[3] = {first_name, second_name, third_name};
    Z3_sort field_sorts[3] = {alpha, beta, alpha};  // Use type variables
    unsigned sort_refs[3] = {0, 0, 0};  // Not recursive references
    
    Z3_constructor mk_triple_con = Z3_mk_constructor(
        ctx, mk_triple_name, is_triple_name, 3, field_names, field_sorts, sort_refs
    );
    
    // Create the parametric datatype using Z3_mk_polymorphic_datatype
    Z3_constructor constructors[1] = {mk_triple_con};
    Z3_sort type_params[2] = {alpha, beta};
    Z3_sort triple = Z3_mk_polymorphic_datatype(ctx, triple_name, 2, type_params, 1, constructors);
    
    Z3_del_constructor(ctx, mk_triple_con);
    
    std::cout << "Created parametric triple datatype using Z3_mk_polymorphic_datatype\n";
    std::cout << "triple sort: " << Z3_sort_to_string(ctx, triple) << "\n";
    
    // Now instantiate the datatype with concrete types
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    
    // Create (triple Int Bool)
    Z3_sort params_int_bool[2] = {int_sort, bool_sort};
    Z3_sort triple_int_bool = Z3_mk_datatype_sort(ctx, triple_name, 2, params_int_bool);
    
    std::cout << "Instantiated triple with Int and Bool\n";
    std::cout << "triple_int_bool: " << Z3_sort_to_string(ctx, triple_int_bool) << "\n";
    
    // Get constructors and accessors from the instantiated datatype
    [[maybe_unused]] Z3_func_decl mk_triple_int_bool = Z3_get_datatype_sort_constructor(ctx, triple_int_bool, 0);
    Z3_func_decl first_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 0);
    [[maybe_unused]] Z3_func_decl second_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 1);
    Z3_func_decl third_int_bool = Z3_get_datatype_sort_constructor_accessor(ctx, triple_int_bool, 0, 2);
    
    std::cout << "Got constructors and accessors from instantiated datatype\n";
    
    // Create a constant t : (triple Int Bool)
    Z3_symbol t_sym = Z3_mk_string_symbol(ctx, "t");
    Z3_ast t = Z3_mk_const(ctx, t_sym, triple_int_bool);
    
    // Create (first t) - should be Int
    Z3_ast first_t = Z3_mk_app(ctx, first_int_bool, 1, &t);
    
    // Create (third t) - should also be Int
    Z3_ast third_t = Z3_mk_app(ctx, third_int_bool, 1, &t);
    
    // Create the equality (= (first t) (third t))
    Z3_ast eq = Z3_mk_eq(ctx, first_t, third_t);
    
    std::cout << "Created term: " << Z3_ast_to_string(ctx, eq) << "\n";
    
    // Verify the term was created successfully
    ENSURE(eq != nullptr);
    
    // Check that first_t and third_t have the same sort (Int)
    Z3_sort first_t_sort = Z3_get_sort(ctx, first_t);
    Z3_sort third_t_sort = Z3_get_sort(ctx, third_t);
    
    std::cout << "Sort of (first t): " << Z3_sort_to_string(ctx, first_t_sort) << "\n";
    std::cout << "Sort of (third t): " << Z3_sort_to_string(ctx, third_t_sort) << "\n";
    
    // Both should be Int
    ENSURE(Z3_is_eq_sort(ctx, first_t_sort, int_sort));
    ENSURE(Z3_is_eq_sort(ctx, third_t_sort, int_sort));
    
    std::cout << "test_polymorphic_datatype_api passed!\n";
    
    Z3_del_context(ctx);
}

static void test_nested_datatype_declaration_printing() {
    std::cout << "test_nested_datatype_declaration_printing\n";

    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_symbol v_name = Z3_mk_string_symbol(ctx, "V");
    Z3_sort v_ref = Z3_mk_datatype_sort(ctx, v_name, 0, nullptr);
    Z3_sort string_sort = Z3_mk_string_sort(ctx);
    Z3_sort array_sort = Z3_mk_array_sort(ctx, string_sort, v_ref);
    Z3_sort int_sort = Z3_mk_int_sort(ctx);

    Z3_symbol num_fields[1] = { Z3_mk_string_symbol(ctx, "n") };
    Z3_sort num_sorts[1] = { int_sort };
    unsigned num_refs[1] = { 0 };
    Z3_constructor num = Z3_mk_constructor(
        ctx, Z3_mk_string_symbol(ctx, "num"), Z3_mk_string_symbol(ctx, "is_num"),
        1, num_fields, num_sorts, num_refs);

    Z3_symbol obj_fields[1] = { Z3_mk_string_symbol(ctx, "o") };
    Z3_sort obj_sorts[1] = { array_sort };
    unsigned obj_refs[1] = { 0 };
    Z3_constructor obj = Z3_mk_constructor(
        ctx, Z3_mk_string_symbol(ctx, "obj"), Z3_mk_string_symbol(ctx, "is_obj"),
        1, obj_fields, obj_sorts, obj_refs);

    Z3_constructor constructors[2] = { num, obj };
    Z3_sort v = Z3_mk_datatype(ctx, v_name, 2, constructors);
    Z3_del_constructor(ctx, num);
    Z3_del_constructor(ctx, obj);

    Z3_ast c = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, "c"), v);
    Z3_ast formula = Z3_mk_eq(ctx, c, c);
    std::string benchmark = Z3_benchmark_to_smtlib_string(
        ctx, "nested-datatype", "ALL", "unknown", "", 0, nullptr, formula);
    ENSURE(benchmark.find("(declare-datatypes ((V 0))") != std::string::npos);
    ENSURE(benchmark.find("(Array String V)") != std::string::npos);

    Z3_solver solver = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, solver);
    Z3_solver_assert(ctx, solver, formula);
    std::string solver_text = Z3_solver_to_string(ctx, solver);
    ENSURE(solver_text.find("(declare-datatypes ((V 0))") != std::string::npos);
    ENSURE(solver_text.find("(Array String V)") != std::string::npos);
    Z3_solver_dec_ref(ctx, solver);

    Z3_del_context(ctx);
}

static void test_smt2_parametric_datatype_is_constructor() {
    std::cout << "test_smt2_parametric_datatype_is_constructor\n";

    cmd_context ctx;
    std::stringstream smtlib_input;
    smtlib_input << "(set-logic ALL)\n"
                 << "(declare-datatypes ((Maybe 1)) ((par (a) ((Nothing) (Just (Just_sel a))))))\n"
                 << "(declare-const x Int)\n"
                 << "(assert ((_ is Just) (Just x)))\n"
                 << "(check-sat)\n";
    ENSURE(parse_smt2_commands(ctx, smtlib_input));
    smt_params params;
    smt::context smt_ctx(ctx.m(), params);
    for (expr* a : ctx.assertions())
        smt_ctx.assert_expr(a);
    ENSURE(l_true == smt_ctx.check());
}

static void test_subterm_declarations() {
    char const* prelude =
        "(declare-datatypes ((Lst 1)) ((par (X) ((lnil) (lcons (lh X) (lt (Lst X)))))))\n";
    for (char const* field : {"(Lst T)", "(Lst (Lst T))", "(Array Int T)", "(Seq T)"}) {
        cmd_context ctx;
        std::ostringstream out;
        ctx.set_regular_stream(out);
        std::istringstream input(std::string(prelude) +
            "(declare-datatype T ((leaf) (node (ch " + field + "))) :subterm sub)\n");
        ENSURE(!parse_smt2_commands(ctx, input));
        ENSURE(out.str().find("subterm predicates are not supported for nested or mutually recursive datatypes") != std::string::npos);
    }

    char const* controls[] = {
        "(declare-datatype T ((leaf) (node (ch T))) :subterm sub)\n"
        "(assert (sub leaf (node leaf)))",
        "(declare-datatype T ((leaf) (node (ch T) (data (Lst Int)))) :subterm sub)\n"
        "(assert (sub leaf (node leaf lnil)))",
        "(declare-datatype T (par (X) ((leaf) (node (ch (T X))))) :subterm sub)\n"
        "(declare-const t (T Int))\n"
        "(assert (sub (as leaf (T Int)) (node (as leaf (T Int)))))",
        "(declare-datatype T ((leaf) (node (ch (Lst T)))))\n"
        "(declare-const t T)\n"
        "(assert (= t (node (lcons leaf lnil))))"
    };
    for (char const* control : controls) {
        cmd_context ctx;
        std::istringstream input(std::string(prelude) + control);
        ENSURE(parse_smt2_commands(ctx, input));
        smt_params params;
        smt::context smt_ctx(ctx.m(), params);
        for (expr* a : ctx.assertions())
            smt_ctx.assert_expr(a);
        ENSURE(l_true == smt_ctx.check());
    }
}

static void test_array_field_cardinality() {
    struct test_case {
        char const* domain;
        char const* field;
        sort_size expected;
    };
    test_case cases[] = {
        {"Bool", "(Array T One)", sort_size(1)},
        {"Int", "(Array T One)", sort_size(1)},
        {"(_ BitVec 64)", "(Array T One)", sort_size(1)},
        {"Bool", "(Array T Bool One)", sort_size(1)},
        {"Int", "(Array T Bool One)", sort_size(1)},
        {"(_ BitVec 64)", "(Array T Bool One)", sort_size(1)},
        {"Bool", "(Array T Bool)", sort_size(4)},
        {"Bool", "(Array T Bool Bool)", sort_size(16)},
        {"Int", "(Array T Bool)", sort_size::mk_infinite()},
        {"(_ BitVec 64)", "(Array T Bool)", sort_size::mk_very_big()},
        {"Bool", "(Array T Int)", sort_size::mk_infinite()},
        {"Bool", "(Array T (_ BitVec 64))", sort_size::mk_very_big()}
    };
    for (auto const& test : cases) {
        std::string input =
            "(declare-datatypes () ((One one)))\n"
            "(declare-datatypes ((Box 1)) ((par (T) ((box (value " +
            std::string(test.field) + "))))))\n"
            "(declare-const b (Box " + test.domain + "))\n";
        cmd_context cmd;
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        sort_size const& actual = cmd.find_func_decl(symbol("b"))->get_range()->get_num_elements();
        VERIFY(actual.is_finite() == test.expected.is_finite());
        VERIFY(actual.is_infinite() == test.expected.is_infinite());
        VERIFY(actual.is_very_big() == test.expected.is_very_big());
        if (test.expected.is_finite())
            VERIFY(actual.size() == test.expected.size());
    }
}

static void check_datatype_commands(char const* input, char const* expected) {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    std::string actual = Z3_eval_smtlib2_string(ctx, input);
    if (actual != expected)
        std::cout << input << "\n" << actual;
    ENSURE(actual == expected);
    Z3_del_context(ctx);
}

static void test_inferred_match_constructor() {
    check_datatype_commands(
        "(declare-datatype O (par (X) ((none) (some (val X)))))\n"
        "(assert (= 1 (match (some 3) ((none 0) (z 1)))))\n"
        "(check-sat)\n", "sat\n");
    check_datatype_commands(
        "(declare-datatype O (par (X) ((none) (some (val X)))))\n"
        "(assert (forall ((x Int)) (= 1 (match (some x) ((none 0) (z 1))))))\n"
        "(check-sat)\n", "sat\n");
    check_datatype_commands(
        "(declare-datatype O (par (X) ((none) (some (val X)))))\n"
        "(declare-const b (O Bool))\n"
        "(assert (= 0 (match (some 3) ((none 0) ((some x) 1)))))\n"
        "(check-sat)\n", "unsat\n");
}

static void test_sequence_field_occurs_check() {
    char const* prelude =
        "(declare-datatype R ((rl) (rn (rc (Seq R)))))\n"
        "(declare-const x R)\n"
        "(declare-const s (Seq R))\n"
        "(declare-const t (Seq R))\n";
    for (char const* cycle : {
            "(assert (= x (rn (seq.++ (seq.unit x) t))))\n",
            "(assert (= x (rn s)))\n(assert (> (seq.len s) 0))\n"
            "(assert (= (seq.nth s 0) x))\n",
            "(assert (= s (seq.unit x)))\n"
            "(assert (= x (rn (seq.++ s t))))\n"}) {
        std::string input = std::string(prelude) + cycle + "(check-sat)\n";
        check_datatype_commands(input.c_str(), "unsat\n");
    }
    std::string input = std::string(prelude) +
        "(assert (= x (rn s)))\n"
        "(push)\n"
        "(assert (> (seq.len s) 0))\n"
        "(assert (= (seq.nth s 0) x))\n"
        "(check-sat)\n"
        "(pop)\n"
        "(assert (= (seq.len s) 0))\n"
        "(assert (= (seq.nth s 0) x))\n"
        "(check-sat)\n";
    check_datatype_commands(input.c_str(), "unsat\nsat\n");
}

static void test_subterm_recursive_polarity() {
    char const* declarations =
        "(declare-datatype L ((nil) (cons (hd Int) (tl L))) :subterm sub)\n"
        "(declare-const x L)\n"
        "(declare-const y L)\n";
    for (unsigned relevancy : {0, 2}) {
        std::string prelude = "(set-option :smt.relevancy " + std::to_string(relevancy) + ")\n" + declarations;
        std::string input = prelude +
            "(assert (sub x y))\n(assert (sub y x))\n(assert (distinct x y))\n(check-sat)\n";
        check_datatype_commands(input.c_str(), "unsat\n");
        input = prelude +
            "(assert (= y (cons 1 (cons 2 nil))))\n"
            "(assert ((_ is cons) x))\n(assert (= (hd x) 3))\n"
            "(assert (sub x y))\n(check-sat)\n";
        check_datatype_commands(input.c_str(), "unsat\n");
        input = prelude +
            "(assert (= y (cons 1 (cons 2 nil))))\n"
            "(assert (= x (cons 2 nil)))\n(assert (sub x y))\n(check-sat)\n";
        check_datatype_commands(input.c_str(), "sat\n");
        input = prelude +
            "(assert (= x (cons 2 nil)))\n(assert (sub x y))\n"
            "(push)\n(assert (= y nil))\n(check-sat)\n(pop)\n"
            "(assert (= y (cons 1 x)))\n(check-sat)\n";
        check_datatype_commands(input.c_str(), "unsat\nsat\n");
        input = prelude +
            "(assert (= x (cons 2 nil)))\n(assert (= y (cons 1 nil)))\n"
            "(assert (not (sub x y)))\n(check-sat)\n";
        check_datatype_commands(input.c_str(), "sat\n");
    }
}

void tst_parametric_datatype() {
    test_inferred_match_constructor();
    test_sequence_field_occurs_check();
    test_subterm_recursive_polarity();
    test_polymorphic_datatype_api();
    test_nested_datatype_declaration_printing();
    test_smt2_parametric_datatype_is_constructor();
    test_subterm_declarations();
    test_array_field_cardinality();
}
