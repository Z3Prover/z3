/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    for_each_ast.cpp

Abstract:

    For each ast visitor

Author:

    Leonardo de Moura (leonardo) 2006-10-18.

Revision History:

--*/

#include"for_each_ast.h"

struct ast_counter_proc {
    unsigned m_num;
    ast_counter_proc():m_num(0) {}
    void operator()(ast *) { m_num++; } 
};

unsigned get_num_nodes(ast * n) {
    for_each_ast_proc<ast_counter_proc> counter;
    for_each_ast(counter, n);
    return counter.m_num;
}


bool for_each_parameter(ptr_vector<ast> & stack, ast_mark & visited, unsigned num_args, parameter const * params) {
    bool result = true;
    for (unsigned i = 0; i < num_args; i++) {
        parameter const& p = params[i];
        if (p.is_ast() && !visited.is_marked(p.get_ast())) {
            stack.push_back(p.get_ast());
            result = false;
        }
    }
    return result;    
}
