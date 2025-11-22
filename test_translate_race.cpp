// Test to reproduce the race condition in Z3_solver_translate
#include <iostream>
#include <thread>
#include <vector>
#include "z3.h"

void test_thread() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx1 = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    
    Z3_solver s = Z3_mk_solver(ctx1);
    Z3_solver_inc_ref(ctx1, s);
    
    // Create variables
    Z3_sort int_sort = Z3_mk_int_sort(ctx1);
    Z3_symbol x_sym = Z3_mk_string_symbol(ctx1, "x");
    Z3_symbol y_sym = Z3_mk_string_symbol(ctx1, "y");
    Z3_ast x = Z3_mk_const(ctx1, x_sym, int_sort);
    Z3_ast y = Z3_mk_const(ctx1, y_sym, int_sort);
    Z3_inc_ref(ctx1, x);
    Z3_inc_ref(ctx1, y);
    
    // Add constraints: y < 2
    Z3_ast two = Z3_mk_int(ctx1, 2, int_sort);
    Z3_inc_ref(ctx1, two);
    Z3_ast y_lt_2 = Z3_mk_lt(ctx1, y, two);
    Z3_inc_ref(ctx1, y_lt_2);
    Z3_solver_assert(ctx1, s, y_lt_2);
    
    // Add constraints: x * y = -2
    Z3_ast neg_two = Z3_mk_int(ctx1, -2, int_sort);
    Z3_inc_ref(ctx1, neg_two);
    Z3_ast args[] = {x, y};
    Z3_ast mul = Z3_mk_mul(ctx1, 2, args);
    Z3_inc_ref(ctx1, mul);
    Z3_ast eq = Z3_mk_eq(ctx1, mul, neg_two);
    Z3_inc_ref(ctx1, eq);
    Z3_solver_assert(ctx1, s, eq);
    
    // Create new context and translate
    Z3_config cfg2 = Z3_mk_config();
    Z3_context ctx2 = Z3_mk_context(cfg2);
    Z3_del_config(cfg2);
    
    Z3_solver s2 = Z3_solver_translate(ctx1, s, ctx2);
    Z3_solver_inc_ref(ctx2, s2);
    
    // Check satisfiability
    Z3_lbool result = Z3_solver_check(ctx2, s2);
    
    if (result != Z3_L_TRUE) {
        std::cerr << "Thread " << std::this_thread::get_id() 
                  << " got unexpected result: " << result 
                  << " (expected SAT)" << std::endl;
    }
    
    // Cleanup
    Z3_solver_dec_ref(ctx2, s2);
    Z3_del_context(ctx2);
    Z3_dec_ref(ctx1, eq);
    Z3_dec_ref(ctx1, mul);
    Z3_dec_ref(ctx1, neg_two);
    Z3_dec_ref(ctx1, y_lt_2);
    Z3_dec_ref(ctx1, two);
    Z3_dec_ref(ctx1, y);
    Z3_dec_ref(ctx1, x);
    Z3_solver_dec_ref(ctx1, s);
    Z3_del_context(ctx1);
}

int main() {
    std::vector<std::thread> threads;
    
    // Create multiple threads (more than CPU cores to trigger the issue)
    for (int i = 0; i < 20; ++i) {
        threads.emplace_back(test_thread);
    }
    
    // Join all threads
    for (auto& t : threads) {
        t.join();
    }
    
    std::cout << "Test completed" << std::endl;
    return 0;
}
