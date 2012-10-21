/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    use_list.cpp

Abstract:

    Use list term index.

Author:

    Leonardo de Moura (leonardo) 2008-02-04.

Revision History:

--*/
#include"use_list.h"

void app_use_list::inc_ref(app * n) {
    if (n->get_num_args() == 0)
        return; // ignore constants
    unsigned id = n->get_id();
    unsigned c  = m_ref_counter.get(id, 0);
    m_ref_counter.setx(id, c+1, 0);
    if (c == 0)
        m_todo.push_back(n);
}

void app_use_list::dec_ref(app * n) {
    if (n->get_num_args() == 0)
        return; // ignore constants
    unsigned id = n->get_id();
    SASSERT(m_ref_counter[id] > 0);
    m_ref_counter[id]--;
    if (m_ref_counter[id] == 0) 
        m_todo.push_back(n);
}

void app_use_list::insert(expr * n) {
    if (is_var(n)) 
        return; // nothing to index
    SASSERT(m_todo.empty());
    inc_ref(to_app(n));
    while (!m_todo.empty()) {
        app * n = m_todo.back();
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * c = n->get_arg(i);
            if (is_var(c)) {
                if (!m_ignore_vars) 
                    use_list<app*>::insert(n, c);
            }
            else {
                SASSERT(is_app(c));
                use_list<app*>::insert(n, c);
                inc_ref(to_app(c));
            }
        }
    }
}

void app_use_list::erase(expr * n) {
    if (is_var(n)) 
        return; // nothing to index
    SASSERT(m_todo.empty());
    dec_ref(to_app(n));
    while (!m_todo.empty()) {
        app * n = m_todo.back();
        unsigned num_args = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * c = n->get_arg(i);
            if (is_var(c)) {
                if (!m_ignore_vars) 
                    use_list<app*>::erase(n, c);
            }
            else {
                SASSERT(is_app(c));
                use_list<app*>::erase(n, c);
                dec_ref(to_app(c));
            }
        }
    }
}
    
void app_use_list::reset() {
    use_list<app*>::reset();
    m_ref_counter.reset();
}
