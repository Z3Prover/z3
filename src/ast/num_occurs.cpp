/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    num_occurs.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-27.

Revision History:

--*/

#include"num_occurs.h"

void num_occurs::process(expr * t, expr_fast_mark1 & visited) {
    ptr_buffer<expr, 128> stack;
    
#define VISIT(ARG) {                                                                                    \
        if (!m_ignore_ref_count1 || ARG->get_ref_count() > 1) {                                         \
            obj_map<expr, unsigned>::obj_map_entry * entry = m_num_occurs.insert_if_not_there2(ARG, 0); \
            entry->get_data().m_value++;                                                                \
        }                                                                                               \
        if (!visited.is_marked(ARG)) {                                                                  \
            visited.mark(ARG, true);                                                                    \
            stack.push_back(ARG);                                                                       \
        }                                                                                               \
    }

    VISIT(t);

    while (!stack.empty()) {
        expr * t = stack.back();
        stack.pop_back();
        unsigned j;
        switch (t->get_kind()) {
        case AST_APP:
            j = to_app(t)->get_num_args();
            while (j > 0) {
                --j;
                expr * arg = to_app(t)->get_arg(j);
                VISIT(arg);
            }
            break;
        case AST_QUANTIFIER:
            if (!m_ignore_quantifiers) {
                expr * child = to_quantifier(t)->get_expr();
                VISIT(child);
            }
            break;
        default:
            break;
        }
    }
}

void num_occurs::operator()(expr * t) {
    expr_fast_mark1   visited;
    process(t, visited);
}

void num_occurs::operator()(unsigned num, expr * const * ts) {
    expr_fast_mark1   visited;
    for (unsigned i = 0; i < num; i++) {
        process(ts[i], visited);
    }
}

