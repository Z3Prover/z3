/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_abstract.h

Abstract:

    Abstract occurrences of constants to bound variables.

Author:

    Nikolaj Bjorner (nbjorner) 2008-03-08

Notes:

--*/    

#include "expr_abstract.h"
#include "map.h"

void expr_abstract(ast_manager& m, unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref&  result) {
    ast_ref_vector pinned(m);
    ptr_vector<expr> stack;
    obj_map<expr, expr*> map;
    expr * curr = 0, *b = 0;
    SASSERT(n->get_ref_count() > 0);

    stack.push_back(n);

    for (unsigned i = 0; i < num_bound; ++i) {
        b = bound[i];
        expr* v = m.mk_var(base + num_bound - i - 1, m.get_sort(b));
        pinned.push_back(v);
        map.insert(b, v);
    }

    while(!stack.empty()) {
        curr = stack.back();
        if (map.contains(curr)) {
            stack.pop_back();
            continue;
        }
        switch(curr->get_kind()) {
        case AST_VAR: {
            map.insert(curr, curr);
            stack.pop_back();
            break;
        }
        case AST_APP: {
            app* a = to_app(curr);
            bool all_visited = true;
            ptr_vector<expr> args;
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                if (!map.find(a->get_arg(i), b)) {
                    stack.push_back(a->get_arg(i));
                    all_visited = false;
                }
                else {
                    args.push_back(b);
                }
            }
            if (all_visited) {
                b = m.mk_app(a->get_decl(), args.size(), args.c_ptr());
                pinned.push_back(b);
                map.insert(curr, b);
                stack.pop_back();
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(curr);
            expr_ref_buffer patterns(m);
            expr_ref result1(m);
            unsigned new_base = base + q->get_num_decls();
        
            for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
                expr_abstract(m, new_base, num_bound, bound, q->get_pattern(i), result1);
                patterns.push_back(result1.get());
            }
            expr_abstract(m, new_base, num_bound, bound, q->get_expr(), result1);
            b = m.update_quantifier(q, patterns.size(), patterns.c_ptr(), result1.get());
            pinned.push_back(b);            
            map.insert(curr, b);
            stack.pop_back();            
            break;
        }
        default:
            UNREACHABLE();
        }
    }
    if (!map.find(n, b)) {
        UNREACHABLE();
    }
    result = b;
}
