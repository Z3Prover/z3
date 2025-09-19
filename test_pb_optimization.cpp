#include "z3++.h"
#include <iostream>

using namespace z3;

void test_pb_max_pattern() {
    std::cout << "Testing PB max pattern detection\n";
    
    context c;
    
    // Create boolean variables
    expr x1 = c.bool_const("x1");
    expr x2 = c.bool_const("x2");
    expr x3 = c.bool_const("x3");
    expr y1 = c.bool_const("y1");
    expr y2 = c.bool_const("y2");
    expr z1 = c.bool_const("z1");
    expr z2 = c.bool_const("z2");
    expr z3 = c.bool_const("z3");
    
    // Create PB constraints like weighted sums
    expr pb1 = 2*ite(x1, c.int_val(1), c.int_val(0)) + 3*ite(x2, c.int_val(1), c.int_val(0)) + ite(x3, c.int_val(1), c.int_val(0));  // potential max = 6
    expr pb2 = ite(y1, c.int_val(1), c.int_val(0)) + 2*ite(y2, c.int_val(1), c.int_val(0));                     // potential max = 3  
    expr pb3 = ite(z1, c.int_val(1), c.int_val(0)) + ite(z2, c.int_val(1), c.int_val(0)) + ite(z3, c.int_val(1), c.int_val(0));       // potential max = 3
    
    optimize opt(c);
    
    // The pattern the issue might be referring to:
    // Instead of maximizing pb1 + pb2 + pb3 directly,
    // we should detect the pattern and introduce auxiliary variables
    
    // Current approach: maximize pb1 + pb2 + pb3
    opt.maximize(pb1 + pb2 + pb3);
    
    std::cout << "check: " << opt.check() << std::endl;
    
    if (opt.check() == sat) {
        model m = opt.get_model();
        std::cout << "Model: " << m << std::endl;
        
        // Get objective values
        std::cout << "Objectives: " << opt.objectives().size() << std::endl;
    }
}

void test_pb_max_with_constraints() {
    std::cout << "\nTesting what the issue might want - auxiliary variables\n";
    
    context c;
    
    // Create boolean variables
    expr x1 = c.bool_const("x1");
    expr x2 = c.bool_const("x2");
    expr y1 = c.bool_const("y1");
    expr y2 = c.bool_const("y2");
    
    // PB expressions
    expr pb1 = 2*ite(x1, c.int_val(1), c.int_val(0)) + ite(x2, c.int_val(1), c.int_val(0));  // max = 3
    expr pb2 = ite(y1, c.int_val(1), c.int_val(0)) + 2*ite(y2, c.int_val(1), c.int_val(0));  // max = 3
    
    optimize opt(c);
    
    // What the issue might want: auxiliary variables p_k for each threshold k
    // For pb1: p1_1, p1_2, p1_3 where pb1 >= k => p1_k
    // For pb2: p2_1, p2_2, p2_3 where pb2 >= k => p2_k
    // Then maximize: p1_1 + p1_2 + p1_3 + p2_1 + p2_2 + p2_3
    
    expr p1_1 = c.bool_const("p1_1");
    expr p1_2 = c.bool_const("p1_2");
    expr p1_3 = c.bool_const("p1_3");
    expr p2_1 = c.bool_const("p2_1");
    expr p2_2 = c.bool_const("p2_2");
    expr p2_3 = c.bool_const("p2_3");
    
    // Add constraints: pb_i >= k => p_k
    opt.add(implies(pb1 >= 1, p1_1));
    opt.add(implies(pb1 >= 2, p1_2));
    opt.add(implies(pb1 >= 3, p1_3));
    opt.add(implies(pb2 >= 1, p2_1));
    opt.add(implies(pb2 >= 2, p2_2));
    opt.add(implies(pb2 >= 3, p2_3));
    
    // Maximize auxiliary variables
    opt.maximize(ite(p1_1, c.int_val(1), c.int_val(0)) + ite(p1_2, c.int_val(1), c.int_val(0)) + ite(p1_3, c.int_val(1), c.int_val(0)) + ite(p2_1, c.int_val(1), c.int_val(0)) + ite(p2_2, c.int_val(1), c.int_val(0)) + ite(p2_3, c.int_val(1), c.int_val(0)));
    
    std::cout << "check: " << opt.check() << std::endl;
    
    if (opt.check() == sat) {
        model m = opt.get_model();
        std::cout << "Model: " << m << std::endl;
        
        // Evaluate original PB expressions
        std::cout << "pb1 = " << m.eval(pb1) << std::endl;
        std::cout << "pb2 = " << m.eval(pb2) << std::endl;
        
        std::cout << "Objectives: " << opt.objectives().size() << std::endl;
    }
}

int main() {
    test_pb_max_pattern();
    test_pb_max_with_constraints();
    return 0;
}