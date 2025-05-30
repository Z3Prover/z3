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

#include "ast/expr_abstract.h"
#include "util/map.h"
#include "ast/ast_pp.h"

void expr_abstractor::operator()(unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref& result) {
    
    if (num_bound == 0) {
        result = n;
        return;
    }
    expr * curr = nullptr, *b = nullptr;
    SASSERT(n->get_ref_count() > 0);

    m_stack.push_back(n);

    for (unsigned i = 0; i < num_bound; ++i) {
        b = bound[i];
        expr* v = m.mk_var(base + num_bound - i - 1, b->get_sort());
        m_pinned.push_back(v);
        m_map.insert(b, v);
    }

    while(!m_stack.empty()) {
        curr = m_stack.back();
        auto &val = m_map.insert_if_not_there(curr, nullptr);
        if (val) {
            m_stack.pop_back();
            continue;
        }
        switch(curr->get_kind()) {
        case AST_VAR: {
            val = curr;
            m_stack.pop_back();
            break;
        }
        case AST_APP: {
            app* a = to_app(curr);
            bool all_visited = true;
            bool changed = false;
            m_args.reset();
            for (unsigned i = 0, e = a->get_num_args(); i < e; ++i) {
                if (!all_visited || !m_map.find(a->get_arg(i), b)) {
                    m_stack.push_back(a->get_arg(i));
                    all_visited = false;
                }
                else {
                    changed |= b != a->get_arg(i);
                    m_args.push_back(b);
                }
            }
            if (all_visited) {
                if (changed) {
                    b = m.mk_app(a->get_decl(), m_args.size(), m_args.data());
                    m_pinned.push_back(b);
                } else {
                    b = curr;
                }
                val = b;
                m_stack.pop_back();
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(curr);
            expr_ref_buffer patterns(m);
            expr_ref result1(m);
            unsigned new_base = base + q->get_num_decls();
        
            for (unsigned i = 0, e = q->get_num_patterns(); i < e; ++i) {
                result1 = expr_abstract(m, new_base, num_bound, bound, q->get_pattern(i));
                patterns.push_back(result1.get());
            }
            result1 = expr_abstract(m, new_base, num_bound, bound, q->get_expr());
            b = m.update_quantifier(q, patterns.size(), patterns.data(), result1.get());
            m_pinned.push_back(b);            
            val = b;
            m_stack.pop_back();            
            break;
        }
        default:
            UNREACHABLE();
        }
    }
    VERIFY (m_map.find(n, b));
    result = b;
    m_pinned.reset();
    m_map.reset();
    m_stack.reset();
    m_args.reset();   
}

void expr_abstract(ast_manager& m, unsigned base, unsigned num_bound, expr* const* bound, expr* n, expr_ref&  result) {
    expr_abstractor abs(m);
    abs(base, num_bound, bound, n, result);
    TRACE(expr_abstract,
          tout << expr_ref(n, m) << "\n";
          tout << result << "\n";);
}

static expr_ref mk_quantifier(quantifier_kind k, ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    expr_ref result(m);
    expr_abstract(m, 0, num_bound, (expr* const*)bound, n, result);    
    if (num_bound > 0) {
        ptr_vector<sort> sorts;
        svector<symbol> names;
        for (unsigned i = 0; i < num_bound; ++i) {
            sorts.push_back(bound[i]->get_sort());
            names.push_back(bound[i]->get_decl()->get_name());
        }
        result = m.mk_quantifier(k, num_bound, sorts.data(), names.data(), result);
    }
    TRACE(expr_abstract,
          tout << expr_ref(n, m) << "\n";
          for (unsigned i = 0; i < num_bound; ++i) tout << expr_ref(bound[i], m) << " ";
          tout << "\n";
          tout << result << "\n";);
    return result;

}

expr_ref mk_forall(ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    return mk_quantifier(forall_k, m, num_bound, bound, n);
}

expr_ref mk_exists(ast_manager& m, unsigned num_bound, app* const* bound, expr* n) {
    return mk_quantifier(exists_k, m, num_bound, bound, n);
}
