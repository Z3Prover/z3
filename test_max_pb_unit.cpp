/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    test_pb_max_optimization.cpp

Abstract:

    Test for max PB constraints optimization feature

Author:

    GitHub Copilot 2024-12-19

--*/

#include "opt/opt_context.h"
#include "ast/arith_decl_plugin.h"
#include "util/trace.h"

void test_max_pb_optimization() {
    ast_manager m;
    opt::context ctx(m);
    arith_util arith(m);
    
    // Create boolean variables
    expr_ref x1(m.mk_const(symbol("x1"), m.mk_bool_sort()), m);
    expr_ref x2(m.mk_const(symbol("x2"), m.mk_bool_sort()), m);
    expr_ref y1(m.mk_const(symbol("y1"), m.mk_bool_sort()), m);
    expr_ref y2(m.mk_const(symbol("y2"), m.mk_bool_sort()), m);
    
    // Create PB constraints as integer expressions
    expr_ref pb1(arith.mk_add(
        arith.mk_mul(arith.mk_numeral(rational(2), true), 
                     m.mk_ite(x1, arith.mk_numeral(rational(1), true), arith.mk_numeral(rational(0), true))),
        m.mk_ite(x2, arith.mk_numeral(rational(1), true), arith.mk_numeral(rational(0), true))), m);
    
    expr_ref pb2(arith.mk_add(
        m.mk_ite(y1, arith.mk_numeral(rational(1), true), arith.mk_numeral(rational(0), true)),
        arith.mk_mul(arith.mk_numeral(rational(2), true),
                     m.mk_ite(y2, arith.mk_numeral(rational(1), true), arith.mk_numeral(rational(0), true)))), m);
    
    // Add two maximize objectives
    ctx.add_objective(to_app(pb1), true);  // maximize
    ctx.add_objective(to_app(pb2), true);  // maximize
    
    // Check optimization
    expr_ref_vector asms(m);
    lbool result = ctx.optimize(asms);
    
    ENSURE(result == l_true);
    
    std::cout << "Max PB optimization test passed!" << std::endl;
}

int main() {
    try {
        test_max_pb_optimization();
        return 0;
    } catch (std::exception& e) {
        std::cerr << "Test failed: " << e.what() << std::endl;
        return 1;
    }
}