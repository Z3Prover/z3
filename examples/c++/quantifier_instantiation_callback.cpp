/**
 * Example demonstrating the UserPropagator callback for quantifier instantiations in Z3.
 * 
 * This feature was added in Z3 version 4.15.3 and allows user propagators to intercept
 * and control quantifier instantiations using the Z3_solver_propagate_on_binding API.
 * 
 * The callback receives the quantifier and its proposed instantiation, and can return
 * false to discard the instantiation, providing fine-grained control over the
 * quantifier instantiation process.
 * 
 * To compile:
 *   g++ -I /path/to/z3/src/api -I /path/to/z3/src/api/c++ \
 *       quantifier_instantiation_callback.cpp -L /path/to/z3/build -lz3 \
 *       -o quantifier_instantiation_callback
 * 
 * To run:
 *   LD_LIBRARY_PATH=/path/to/z3/build ./quantifier_instantiation_callback
 */

#include <iostream>
#include <vector>
#include <string>
#include <z3++.h>

using namespace z3;
using namespace std;

// Global counter for demonstration purposes
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
 * @return true to allow the instantiation, false to discard it
 */
bool quantifier_instantiation_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    // Cast the context back to our custom data structure if needed
    // For this simple example, we'll use global variables
    
    instantiation_counter++;
    
    // Get string representations for logging
    Z3_context z3_ctx = Z3_solver_callback_get_context(cb);
    string q_str = Z3_ast_to_string(z3_ctx, q);
    string inst_str = Z3_ast_to_string(z3_ctx, inst);
    
    cout << "Instantiation #" << instantiation_counter << ":" << endl;
    cout << "  Quantifier: " << q_str << endl;
    cout << "  Instantiation: " << inst_str << endl;
    
    // Example filtering logic: allow only the first 3 instantiations
    // In practice, you might implement more sophisticated filtering
    bool allow = instantiation_counter <= 3;
    
    if (allow) {
        allowed_counter++;
        cout << "  -> ALLOWED (#" << allowed_counter << ")" << endl;
    } else {
        blocked_counter++;
        cout << "  -> BLOCKED (#" << blocked_counter << ")" << endl;
    }
    
    cout << endl;
    return allow;
}

/**
 * Example demonstrating basic quantifier instantiation control.
 */
void example_basic_control() {
    cout << string(60, '=') << endl;
    cout << "BASIC QUANTIFIER INSTANTIATION CONTROL EXAMPLE" << endl;
    cout << string(60, '=') << endl;
    
    context ctx;
    solver s(ctx);
    
    // Register the quantifier instantiation callback
    Z3_solver_propagate_on_binding(ctx, s, quantifier_instantiation_callback);
    
    // Create a simple quantified formula
    sort int_sort = ctx.int_sort();
    func_decl f = ctx.function("f", int_sort, int_sort);
    expr x = ctx.int_const("x");
    
    // Add quantified axiom: forall x. f(x) >= 0
    expr axiom = forall(x, f(x) >= 0);
    s.add(axiom);
    
    // Add constraints that might trigger instantiations
    expr a = ctx.int_const("a");
    expr b = ctx.int_const("b");
    expr c = ctx.int_const("c");
    
    s.add(f(a) < 10);
    s.add(f(b) < 20);
    s.add(f(c) < 30);
    
    // Add specific values
    s.add(a == 1);
    s.add(b == 2);
    s.add(c == 3);
    
    cout << "Checking satisfiability with instantiation control..." << endl;
    check_result result = s.check();
    cout << "Result: " << result << endl;
    
    if (result == sat) {
        cout << "Model: " << s.get_model() << endl;
    }
    
    // Print statistics
    cout << endl << "Instantiation Statistics:" << endl;
    cout << "  Total attempts: " << instantiation_counter << endl;
    cout << "  Allowed: " << allowed_counter << endl;
    cout << "  Blocked: " << blocked_counter << endl;
}

// Structure to hold callback context data
struct AdvancedCallbackContext {
    int max_instantiations_per_pattern;
    map<string, int> instantiation_counts;
    
    AdvancedCallbackContext(int max_per_pattern = 2) 
        : max_instantiations_per_pattern(max_per_pattern) {}
};

/**
 * Advanced callback that tracks instantiation patterns.
 */
bool advanced_instantiation_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    AdvancedCallbackContext* context = static_cast<AdvancedCallbackContext*>(ctx);
    
    // Get string representation of the instantiation
    Z3_context z3_ctx = Z3_solver_callback_get_context(cb);
    string inst_str = Z3_ast_to_string(z3_ctx, inst);
    
    // Count instantiations for this pattern
    context->instantiation_counts[inst_str]++;
    int count = context->instantiation_counts[inst_str];
    
    // Allow only up to max_instantiations_per_pattern of the same pattern
    bool allow = count <= context->max_instantiations_per_pattern;
    
    cout << "Instantiation: " << inst_str << " (attempt #" << count << ")" << endl;
    cout << "  -> " << (allow ? "ALLOWED" : "BLOCKED") << endl;
    
    return allow;
}

/**
 * Example demonstrating advanced instantiation filtering.
 */
void example_advanced_filtering() {
    cout << endl << string(60, '=') << endl;
    cout << "ADVANCED INSTANTIATION FILTERING EXAMPLE" << endl;
    cout << string(60, '=') << endl;
    
    context ctx;
    solver s(ctx);
    
    // Create callback context
    AdvancedCallbackContext callback_ctx(2); // Allow max 2 instantiations per pattern
    
    // Register the advanced callback
    Z3_solver_propagate_on_binding(ctx, s, advanced_instantiation_callback);
    
    // Store callback context in solver (this is a simplified approach)
    // In practice, you might need a more sophisticated context management system
    
    // Create a more complex scenario
    sort int_sort = ctx.int_sort();
    sort bool_sort = ctx.bool_sort();
    func_decl P = ctx.function("P", int_sort, int_sort, bool_sort);
    
    expr x = ctx.int_const("x");
    expr y = ctx.int_const("y");
    
    // Add quantified formula: forall x, y. P(x, y) => P(y, x)
    expr axiom = forall(x, y, implies(P(x, y), P(y, x)));
    s.add(axiom);
    
    // Add facts that will trigger instantiations
    expr a = ctx.int_const("a");
    expr b = ctx.int_const("b");
    expr c = ctx.int_const("c");
    
    s.add(P(a, b));
    s.add(P(b, c));
    s.add(P(c, a));
    
    cout << "Checking satisfiability with advanced filtering..." << endl;
    check_result result = s.check();
    cout << "Result: " << result << endl;
    
    if (result == sat) {
        cout << "Model: " << s.get_model() << endl;
    }
    
    // Print pattern statistics
    cout << endl << "Instantiation Pattern Statistics:" << endl;
    for (const auto& pair : callback_ctx.instantiation_counts) {
        cout << "  " << pair.first << ": " << pair.second << " attempts" << endl;
    }
}

/**
 * Simple callback that logs all instantiations without blocking any.
 */
bool logging_callback(void* ctx, Z3_solver_callback cb, Z3_ast q, Z3_ast inst) {
    vector<pair<string, string>>* log = static_cast<vector<pair<string, string>>*>(ctx);
    
    Z3_context z3_ctx = Z3_solver_callback_get_context(cb);
    string q_str = Z3_ast_to_string(z3_ctx, q);
    string inst_str = Z3_ast_to_string(z3_ctx, inst);
    
    log->push_back(make_pair(q_str, inst_str));
    
    cout << "Logged instantiation #" << log->size() << ":" << endl;
    cout << "  Quantifier: " << q_str << endl;
    cout << "  Instantiation: " << inst_str << endl;
    
    // Allow all instantiations for logging purposes
    return true;
}

/**
 * Example focused on logging instantiation patterns.
 */
void example_logging() {
    cout << endl << string(60, '=') << endl;
    cout << "INSTANTIATION LOGGING EXAMPLE" << endl;
    cout << string(60, '=') << endl;
    
    context ctx;
    solver s(ctx);
    
    // Create log storage
    vector<pair<string, string>> instantiation_log;
    
    // Register logging callback
    Z3_solver_propagate_on_binding(ctx, s, logging_callback);
    
    // Create scenario with multiple quantifiers
    sort int_sort = ctx.int_sort();
    func_decl f = ctx.function("f", int_sort, int_sort);
    func_decl g = ctx.function("g", int_sort, int_sort);
    
    expr x = ctx.int_const("x");
    
    // Add multiple quantified axioms
    s.add(forall(x, f(x) >= x));  // f(x) is at least x
    s.add(forall(x, g(x) <= x));  // g(x) is at most x
    
    // Add constraints to trigger instantiations
    expr a = ctx.int_const("a");
    expr b = ctx.int_const("b");
    
    s.add(f(a) < 5);
    s.add(g(b) > 10);
    s.add(a == 2);
    s.add(b == 8);
    
    cout << "Solving with full logging enabled..." << endl;
    check_result result = s.check();
    cout << "Result: " << result << endl;
    
    // Analyze logged patterns
    cout << endl << "Instantiation Analysis:" << endl;
    cout << "Total instantiations logged: " << instantiation_log.size() << endl;
    
    // Group by quantifier
    map<string, vector<string>> by_quantifier;
    for (const auto& entry : instantiation_log) {
        by_quantifier[entry.first].push_back(entry.second);
    }
    
    for (const auto& pair : by_quantifier) {
        cout << endl << "Quantifier: " << pair.first << endl;
        cout << "  Instantiations (" << pair.second.size() << "):" << endl;
        for (size_t i = 0; i < pair.second.size(); ++i) {
            cout << "    " << (i + 1) << ". " << pair.second[i] << endl;
        }
    }
}

int main() {
    try {
        // Run all examples
        example_basic_control();
        example_advanced_filtering();
        example_logging();
        
        cout << endl << string(60, '=') << endl;
        cout << "All examples completed successfully!" << endl;
        cout << string(60, '=') << endl;
        
    } catch (exception& e) {
        cout << "Exception: " << e.what() << endl;
        return 1;
    }
    
    return 0;
}