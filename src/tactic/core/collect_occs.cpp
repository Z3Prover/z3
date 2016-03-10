/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    collect_cccs.cpp

Abstract:

    Collect variables by occurrences.

Author:

    Leonardo (leonardo) 2011-10-22

Notes:

--*/

#include "ast.h"
#include "goal.h"
#include "hashtable.h"
#include "collect_occs.h"

bool collect_occs::visit(expr * t) {
    if (m_visited.is_marked(t)) {
        if (is_uninterp_const(t))
            m_more_than_once.mark(t);
        return true;
    }
    m_visited.mark(t);
    if (is_uninterp_const(t)) {
        m_vars.push_back(to_app(t));
        return true;
    }
    if (is_var(t))
        return true;
    if (is_app(t) && to_app(t)->get_num_args() == 0)
        return true;
    m_stack.push_back(frame(t, 0));
    return false;
}
    
void collect_occs::process(expr * t) {
    SASSERT(m_stack.empty());
    if (visit(t))
        return;
    SASSERT(!m_stack.empty());
    unsigned num;
    expr * child;
    while (!m_stack.empty()) {
    start:
        frame & fr = m_stack.back();
        expr *  t  = fr.first;
        switch (t->get_kind()) {
        case AST_APP:
            num = to_app(t)->get_num_args();
            while (fr.second < num) {
                child = to_app(t)->get_arg(fr.second);
                fr.second++;
                if (!visit(child))
                    goto start;
            }
            m_stack.pop_back();
            break;
        case AST_QUANTIFIER:
            // don't need to visit patterns
            child = to_quantifier(t)->get_expr();
            fr.second++;
            if (!visit(child))
                goto start;
            m_stack.pop_back();
            break;
        default:
            UNREACHABLE();
        }
    }
}
    
    
void collect_occs::operator()(goal const & g, obj_hashtable<expr> & r) {
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * t = g.form(i);
        process(t);
    }
    
    ptr_vector<app>::const_iterator it  = m_vars.begin();
    ptr_vector<app>::const_iterator end = m_vars.end();
    for (; it != end; ++it) {
        if (m_more_than_once.is_marked(*it))
            continue;
        r.insert(*it);
    }
    m_visited.reset();
    m_more_than_once.reset();
}
