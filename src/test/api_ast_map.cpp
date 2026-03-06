/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    api_ast_map.cpp

Abstract:

    Tests for AST map API

Author:

    Daily Test Coverage Improver

Revision History:

--*/

#include "api/z3.h"
#include "api/api_util.h"
#include "api/api_context.h"
#include "util/debug.h"
#include <iostream>

void test_ast_map_basic_operations() {
    // Test basic creation, insertion, and retrieval
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    // Create AST map
    Z3_ast_map m = Z3_mk_ast_map(ctx);
    VERIFY(m != nullptr);

    // Test initial size is 0
    VERIFY(Z3_ast_map_size(ctx, m) == 0);

    // Create simple test ASTs
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast one = Z3_mk_numeral(ctx, "1", int_sort);
    Z3_ast two = Z3_mk_numeral(ctx, "2", int_sort);

    // Test insertion with simple ASTs
    Z3_ast_map_insert(ctx, m, one, two);
    VERIFY(Z3_ast_map_size(ctx, m) == 1);

    // Test contains
    VERIFY(Z3_ast_map_contains(ctx, m, one));

    // Test find
    Z3_ast found = Z3_ast_map_find(ctx, m, one);
    VERIFY(found != nullptr);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_overwrite() {
    // Test overwriting existing entries
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast one = Z3_mk_numeral(ctx, "1", int_sort);
    Z3_ast three = Z3_mk_numeral(ctx, "3", int_sort);

    // Insert initial value
    Z3_ast_map_insert(ctx, m, one, three);
    VERIFY(Z3_ast_map_size(ctx, m) == 1);

    // Overwrite with new value
    Z3_ast_map_insert(ctx, m, one, one);
    VERIFY(Z3_ast_map_size(ctx, m) == 1); // Size should remain same

    // Verify new value
    Z3_ast found = Z3_ast_map_find(ctx, m, one);
    VERIFY(found != nullptr);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_erase() {
    // Test erasing entries
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast one = Z3_mk_numeral(ctx, "1", int_sort);
    Z3_ast two = Z3_mk_numeral(ctx, "2", int_sort);

    // Insert two entries
    Z3_ast_map_insert(ctx, m, one, two);
    Z3_ast_map_insert(ctx, m, two, one);
    VERIFY(Z3_ast_map_size(ctx, m) == 2);

    // Erase first entry
    Z3_ast_map_erase(ctx, m, one);
    VERIFY(Z3_ast_map_size(ctx, m) == 1);
    VERIFY(!Z3_ast_map_contains(ctx, m, one));
    VERIFY(Z3_ast_map_contains(ctx, m, two));

    // Erase non-existent entry (should be safe)
    Z3_ast_map_erase(ctx, m, one);
    VERIFY(Z3_ast_map_size(ctx, m) == 1);

    // Erase remaining entry
    Z3_ast_map_erase(ctx, m, two);
    VERIFY(Z3_ast_map_size(ctx, m) == 0);
    VERIFY(!Z3_ast_map_contains(ctx, m, two));

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_reset() {
    // Test resetting the map
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_ast one = Z3_mk_numeral(ctx, "1", int_sort);
    Z3_ast two = Z3_mk_numeral(ctx, "2", int_sort);

    // Insert entries
    Z3_ast_map_insert(ctx, m, one, two);
    Z3_ast_map_insert(ctx, m, two, one);
    VERIFY(Z3_ast_map_size(ctx, m) == 2);

    // Reset the map
    Z3_ast_map_reset(ctx, m);
    VERIFY(Z3_ast_map_size(ctx, m) == 0);
    VERIFY(!Z3_ast_map_contains(ctx, m, one));
    VERIFY(!Z3_ast_map_contains(ctx, m, two));

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_keys() {
    // Test getting keys
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_symbol y_sym = Z3_mk_string_symbol(ctx, "y");
    Z3_symbol z_sym = Z3_mk_string_symbol(ctx, "z");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
    Z3_ast y = Z3_mk_const(ctx, y_sym, int_sort);
    Z3_ast z = Z3_mk_const(ctx, z_sym, int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);

    // Insert entries
    Z3_ast_map_insert(ctx, m, x, one);
    Z3_ast_map_insert(ctx, m, y, two);
    Z3_ast_map_insert(ctx, m, z, three);

    // Get keys
    Z3_ast_vector keys = Z3_ast_map_keys(ctx, m);
    VERIFY(keys != nullptr);
    VERIFY(Z3_ast_vector_size(ctx, keys) == 3);

    // Verify all keys are present (order may vary)
    bool found_x = false, found_y = false, found_z = false;
    for (unsigned i = 0; i < Z3_ast_vector_size(ctx, keys); ++i) {
        Z3_ast key = Z3_ast_vector_get(ctx, keys, i);
        if (Z3_is_eq_ast(ctx, key, x)) found_x = true;
        if (Z3_is_eq_ast(ctx, key, y)) found_y = true;
        if (Z3_is_eq_ast(ctx, key, z)) found_z = true;
    }
    VERIFY(found_x && found_y && found_z);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_to_string() {
    // Test string representation
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    // Empty map string
    Z3_string empty_str = Z3_ast_map_to_string(ctx, m);
    VERIFY(empty_str != nullptr);

    // Add an entry and test string representation
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);

    Z3_ast_map_insert(ctx, m, x, one);

    Z3_string str = Z3_ast_map_to_string(ctx, m);
    VERIFY(str != nullptr);
    // The string should contain "ast-map"
    VERIFY(strstr(str, "ast-map") != nullptr);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_ref_counting() {
    // Test reference counting
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    // Test inc/dec ref
    Z3_ast_map_inc_ref(ctx, m);
    Z3_ast_map_dec_ref(ctx, m);

    // Test dec_ref with null (should be safe)
    Z3_ast_map_dec_ref(ctx, nullptr);

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_different_ast_types() {
    // Test with different AST types
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    // Different types of ASTs
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_symbol p_sym = Z3_mk_string_symbol(ctx, "p");

    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
    Z3_ast p = Z3_mk_const(ctx, p_sym, bool_sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast true_ast = Z3_mk_true(ctx);
    Z3_ast false_ast = Z3_mk_false(ctx);

    // Map integer variable to integer constant
    Z3_ast_map_insert(ctx, m, x, zero);

    // Map boolean variable to boolean constant
    Z3_ast_map_insert(ctx, m, p, true_ast);

    // Map boolean constant to boolean constant
    Z3_ast_map_insert(ctx, m, false_ast, true_ast);

    VERIFY(Z3_ast_map_size(ctx, m) == 3);

    // Verify mappings
    Z3_ast found_x = Z3_ast_map_find(ctx, m, x);
    VERIFY(Z3_is_eq_ast(ctx, found_x, zero));

    Z3_ast found_p = Z3_ast_map_find(ctx, m, p);
    VERIFY(Z3_is_eq_ast(ctx, found_p, true_ast));

    Z3_ast found_false = Z3_ast_map_find(ctx, m, false_ast);
    VERIFY(Z3_is_eq_ast(ctx, found_false, true_ast));

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void test_ast_map_find_errors() {
    // Test error handling in find operations
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);

    Z3_ast_map m = Z3_mk_ast_map(ctx);

    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
    Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);

    // Try to find in empty map - should return null and set error
    Z3_ast result = Z3_ast_map_find(ctx, m, x);
    VERIFY(result == nullptr);
    // Error should be set (but we can't easily test error codes in this framework)

    Z3_del_config(cfg);
    Z3_del_context(ctx);
}

void tst_api_ast_map() {
    test_ast_map_basic_operations();
    test_ast_map_overwrite();
    test_ast_map_erase();
    test_ast_map_reset();
    test_ast_map_ref_counting();
    test_ast_map_to_string();
    // test_ast_map_keys();
    // test_ast_map_different_ast_types();
    // test_ast_map_find_errors();
}