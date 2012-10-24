/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    normalize_vars.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-16.

Revision History:

--*/
#include"normalize_vars.h"

expr * normalize_vars::operator()(expr * n) {
    SASSERT(m_todo.empty());
    m_todo.push_back(n);
    while (!m_todo.empty()) {
        n = m_todo.back();
        if (m_cache.contains(n)) {
            m_todo.pop_back();
            continue;
        }
        if (is_var(n)) {
            m_todo.pop_back();
            unsigned idx = to_var(n)->get_idx();
            var * new_var = m_map.get(idx, 0);
            if (new_var == 0) {
                new_var = m_manager.mk_var(m_next_var, to_var(n)->get_sort());
                m_next_var++;
                m_new_vars.push_back(new_var);
                m_map.setx(idx, new_var, 0);
            }
            SASSERT(new_var->get_sort() == to_var(n)->get_sort());
            m_cache.insert(n, new_var);
        }
        else {
            SASSERT(is_app(n));
            bool visited = true;
            unsigned num_args = to_app(n)->get_num_args();
            unsigned j = num_args;
            while (j > 0) {
                --j;
                expr * child = to_app(n)->get_arg(j);
                if (!m_cache.contains(child)) {
                    m_todo.push_back(child);
                    visited = false;
                }
            }
            if (visited) {
                m_todo.pop_back();
                m_new_children.reset();
                bool modified = false;
                for (unsigned i = 0; i < num_args; i++) {
                    expr * child = to_app(n)->get_arg(i);
                    expr * new_child = 0;
                    m_cache.find(child, new_child);
                    SASSERT(new_child);
                    if (child != new_child)
                        modified = true;
                    m_new_children.push_back(new_child);
                }
                if (!modified) 
                    m_cache.insert(n, n);
                else
                    m_cache.insert(n, m_manager.mk_app(to_app(n)->get_decl(), m_new_children.size(), m_new_children.c_ptr()));
            }
        }
    }
    expr * r = 0;
    m_cache.find(n, r);
    SASSERT(r);
    return r;
}
 
void normalize_vars::reset() {
    m_cache.reset();
    m_map.reset();
    m_new_vars.reset();
    m_next_var = 0;
}

