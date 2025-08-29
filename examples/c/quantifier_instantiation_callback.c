/**
 * Example demonstrating the UserPropagator callback for quantifier instantiations in Z3 C API.
 * 
 * This feature was added in Z3 version 4.15.3 and allows user propagators to intercept
 * and control quantifier instantiations using the Z3_solver_propagate_on_binding API.
 * 
 * The callback receives the quantifier and its proposed instantiation, and can return
 * Z3_FALSE to discard the instantiation, providing fine-grained control over the
 * quantifier instantiation process.
 * 
 * To compile:
 *   gcc -I /path/to/z3/src/api quantifier_instantiation_callback.c \
 *       -L /path/to/z3/build -lz3 -o quantifier_instantiation_callback
 * 
 * To run:
 *   LD_LIBRARY_PATH=/path/to/z3/build ./quantifier_instantiation_callback
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <z3.h>

// Global counters for demonstration
static int instantiation_counter = 0;
static int allowed_counter = 0;
static int blocked_counter = 0;

/**
 * User-defined callback for quantifier instantiation control.
 * 
 * This function is called by Z3 whenever it wants to instantiate a quantifier.
 * 
 * @param ctx User context (can be used to pass custom data)
 * @param cb Solver callback object
 * @param q The quantifier being instantiated
 * @param inst The proposed instantiation
 * @return Z3_TRUE to allow the instantiation, Z3_FALSE to discard it
 */
Z3_bool quantifier_instantiation_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    // Get the Z3 context from the callback
    Z3_context z3_ctx = Z3_solver_callback_get_context(cb);
    
    instantiation_counter++;
    
    // Get string representations for logging
    Z3_string q_str = Z3_ast_to_string(z3_ctx, q);
    Z3_string inst_str = Z3_ast_to_string(z3_ctx, inst);
    
    printf("Instantiation #%d:\n", instantiation_counter);
    printf("  Quantifier: %s\n", q_str);
    printf("  Instantiation: %s\n", inst_str);
    
    // Example filtering logic: allow only the first 3 instantiations
    // In practice, you might implement more sophisticated filtering
    Z3_bool allow = (instantiation_counter <= 3) ? Z3_TRUE : Z3_FALSE;
    
    if (allow) {
        allowed_counter++;
        printf("  -> ALLOWED (#%d)\n", allowed_counter);
    } else {
        blocked_counter++;
        printf("  -> BLOCKED (#%d)\n", blocked_counter);
    }
    
    printf("\n");
    return allow;
}

/**
 * Example demonstrating basic quantifier instantiation control.
 */
void example_basic_control() {
    printf("============================================================\n");
    printf("BASIC QUANTIFIER INSTANTIATION CONTROL EXAMPLE\n");
    printf("============================================================\n");
    
    // Create Z3 context and solver
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    // Register the quantifier instantiation callback
    Z3_solver_propagate_on_binding(ctx, s, quantifier_instantiation_callback);
    
    // Create sorts and symbols
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_symbol f_name = Z3_mk_string_symbol(ctx, "f");
    Z3_symbol x_name = Z3_mk_string_symbol(ctx, "x");
    
    // Create function declaration f: Int -> Int
    Z3_func_decl f = Z3_mk_func_decl(ctx, f_name, 1, &int_sort, int_sort);
    
    // Create variables
    Z3_ast x = Z3_mk_bound(ctx, 0, int_sort);
    Z3_ast f_x = Z3_mk_app(ctx, f, 1, &x);
    
    // Create axiom: forall x. f(x) >= 0
    Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
    Z3_ast f_x_geq_0 = Z3_mk_ge(ctx, f_x, zero);
    
    Z3_ast axiom = Z3_mk_forall_const(ctx, 0, 1, &x, 0, NULL, f_x_geq_0);
    Z3_solver_assert(ctx, s, axiom);
    
    // Create constants and add constraints
    Z3_symbol a_name = Z3_mk_string_symbol(ctx, "a");
    Z3_symbol b_name = Z3_mk_string_symbol(ctx, "b");
    Z3_symbol c_name = Z3_mk_string_symbol(ctx, "c");
    
    Z3_ast a = Z3_mk_const(ctx, a_name, int_sort);
    Z3_ast b = Z3_mk_const(ctx, b_name, int_sort);
    Z3_ast c = Z3_mk_const(ctx, c_name, int_sort);
    
    // Add constraints that might trigger instantiations
    Z3_ast f_a = Z3_mk_app(ctx, f, 1, &a);
    Z3_ast f_b = Z3_mk_app(ctx, f, 1, &b);
    Z3_ast f_c = Z3_mk_app(ctx, f, 1, &c);
    
    Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);
    Z3_ast twenty = Z3_mk_int(ctx, 20, int_sort);
    Z3_ast thirty = Z3_mk_int(ctx, 30, int_sort);
    
    Z3_solver_assert(ctx, s, Z3_mk_lt(ctx, f_a, ten));
    Z3_solver_assert(ctx, s, Z3_mk_lt(ctx, f_b, twenty));
    Z3_solver_assert(ctx, s, Z3_mk_lt(ctx, f_c, thirty));
    
    // Add specific values
    Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
    Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
    Z3_ast three = Z3_mk_int(ctx, 3, int_sort);
    
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, a, one));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, b, two));
    Z3_solver_assert(ctx, s, Z3_mk_eq(ctx, c, three));
    
    printf("Checking satisfiability with instantiation control...\n");
    Z3_lbool result = Z3_solver_check(ctx, s);
    
    switch (result) {
        case Z3_L_TRUE:
            printf("Result: SAT\n");
            {
                Z3_model model = Z3_solver_get_model(ctx, s);
                if (model) {
                    Z3_model_inc_ref(ctx, model);
                    printf("Model: %s\n", Z3_model_to_string(ctx, model));
                    Z3_model_dec_ref(ctx, model);
                }
            }
            break;
        case Z3_L_FALSE:
            printf("Result: UNSAT\n");
            break;
        case Z3_L_UNDEF:
            printf("Result: UNKNOWN\n");
            break;
    }
    
    // Print statistics
    printf("\nInstantiation Statistics:\n");
    printf("  Total attempts: %d\n", instantiation_counter);
    printf("  Allowed: %d\n", allowed_counter);
    printf("  Blocked: %d\n", blocked_counter);
    
    // Cleanup
    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

// Structure for advanced callback context
typedef struct {
    int max_instantiations_per_pattern;
    char** patterns;
    int* counts;
    int num_patterns;
    int capacity;
} AdvancedCallbackContext;

/**
 * Find or add a pattern in the context.
 */
int find_or_add_pattern(AdvancedCallbackContext* context, const char* pattern) {
    // Look for existing pattern
    for (int i = 0; i < context->num_patterns; i++) {
        if (strcmp(context->patterns[i], pattern) == 0) {
            return i;
        }
    }
    
    // Add new pattern if space available
    if (context->num_patterns < context->capacity) {
        int index = context->num_patterns++;
        context->patterns[index] = malloc(strlen(pattern) + 1);
        strcpy(context->patterns[index], pattern);
        context->counts[index] = 0;
        return index;
    }
    
    return -1; // No space
}

/**
 * Advanced callback that tracks instantiation patterns.
 */
Z3_bool advanced_instantiation_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    AdvancedCallbackContext* context = (AdvancedCallbackContext*)ctx;
    
    // Get string representation of the instantiation
    Z3_context z3_ctx = Z3_solver_callback_get_context(cb);
    Z3_string inst_str = Z3_ast_to_string(z3_ctx, inst);
    
    // Find or add this pattern
    int pattern_index = find_or_add_pattern(context, inst_str);
    if (pattern_index == -1) {
        printf("Warning: Pattern storage full, allowing instantiation\n");
        return Z3_TRUE;
    }
    
    // Increment count for this pattern
    context->counts[pattern_index]++;
    int count = context->counts[pattern_index];
    
    // Allow only up to max_instantiations_per_pattern of the same pattern
    Z3_bool allow = (count <= context->max_instantiations_per_pattern) ? Z3_TRUE : Z3_FALSE;
    
    printf("Instantiation: %s (attempt #%d)\n", inst_str, count);
    printf("  -> %s\n", allow ? "ALLOWED" : "BLOCKED");
    
    return allow;
}

/**
 * Example demonstrating advanced instantiation filtering.
 */
void example_advanced_filtering() {
    printf("\n============================================================\n");
    printf("ADVANCED INSTANTIATION FILTERING EXAMPLE\n");
    printf("============================================================\n");
    
    // Create callback context
    AdvancedCallbackContext context;
    context.max_instantiations_per_pattern = 2;
    context.capacity = 100;
    context.num_patterns = 0;
    context.patterns = malloc(context.capacity * sizeof(char*));
    context.counts = malloc(context.capacity * sizeof(int));
    
    // Create Z3 context and solver
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    
    // Register the advanced callback with context
    Z3_solver_propagate_on_binding(ctx, s, advanced_instantiation_callback);
    
    // Create sorts and function declaration
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_sort P_domain[2] = {int_sort, int_sort};
    
    Z3_symbol P_name = Z3_mk_string_symbol(ctx, "P");
    Z3_func_decl P = Z3_mk_func_decl(ctx, P_name, 2, P_domain, bool_sort);
    
    // Create bound variables for quantifier
    Z3_ast x = Z3_mk_bound(ctx, 1, int_sort); // Note: index 1 for second variable in binding order
    Z3_ast y = Z3_mk_bound(ctx, 0, int_sort); // Note: index 0 for first variable in binding order
    
    // Create P(x, y) and P(y, x)
    Z3_ast xy_args[2] = {x, y};
    Z3_ast yx_args[2] = {y, x};
    Z3_ast P_xy = Z3_mk_app(ctx, P, 2, xy_args);
    Z3_ast P_yx = Z3_mk_app(ctx, P, 2, yx_args);
    
    // Create implication: P(x, y) => P(y, x)
    Z3_ast implication = Z3_mk_implies(ctx, P_xy, P_yx);
    
    // Create quantified formula: forall x, y. P(x, y) => P(y, x)
    Z3_ast vars[2] = {x, y};
    Z3_ast axiom = Z3_mk_forall_const(ctx, 0, 2, vars, 0, NULL, implication);
    Z3_solver_assert(ctx, s, axiom);
    
    // Create constants
    Z3_symbol a_name = Z3_mk_string_symbol(ctx, "a");
    Z3_symbol b_name = Z3_mk_string_symbol(ctx, "b");
    Z3_symbol c_name = Z3_mk_string_symbol(ctx, "c");
    
    Z3_ast a = Z3_mk_const(ctx, a_name, int_sort);
    Z3_ast b = Z3_mk_const(ctx, b_name, int_sort);
    Z3_ast c = Z3_mk_const(ctx, c_name, int_sort);
    
    // Add facts that will trigger instantiations
    Z3_ast ab_args[2] = {a, b};
    Z3_ast bc_args[2] = {b, c};
    Z3_ast ca_args[2] = {c, a};
    
    Z3_solver_assert(ctx, s, Z3_mk_app(ctx, P, 2, ab_args));
    Z3_solver_assert(ctx, s, Z3_mk_app(ctx, P, 2, bc_args));
    Z3_solver_assert(ctx, s, Z3_mk_app(ctx, P, 2, ca_args));
    
    printf("Checking satisfiability with advanced filtering...\n");
    Z3_lbool result = Z3_solver_check(ctx, s);
    
    switch (result) {
        case Z3_L_TRUE:
            printf("Result: SAT\n");
            {
                Z3_model model = Z3_solver_get_model(ctx, s);
                if (model) {
                    Z3_model_inc_ref(ctx, model);
                    printf("Model: %s\n", Z3_model_to_string(ctx, model));
                    Z3_model_dec_ref(ctx, model);
                }
            }
            break;
        case Z3_L_FALSE:
            printf("Result: UNSAT\n");
            break;
        case Z3_L_UNDEF:
            printf("Result: UNKNOWN\n");
            break;
    }
    
    // Print pattern statistics
    printf("\nInstantiation Pattern Statistics:\n");
    for (int i = 0; i < context.num_patterns; i++) {
        printf("  %s: %d attempts\n", context.patterns[i], context.counts[i]);
    }
    
    // Cleanup context
    for (int i = 0; i < context.num_patterns; i++) {
        free(context.patterns[i]);
    }
    free(context.patterns);
    free(context.counts);
    
    // Cleanup Z3 objects
    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

int main() {
    printf("Z3 Quantifier Instantiation Callback Examples\n");
    printf("==============================================\n\n");
    
    // Run examples
    example_basic_control();
    example_advanced_filtering();
    
    printf("\n============================================================\n");
    printf("All examples completed successfully!\n");
    printf("============================================================\n");
    
    return 0;
}