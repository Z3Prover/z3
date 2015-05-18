/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    ast_counter.cpp

Abstract:

    Routines for counting features of terms, such as free variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-18.

Revision History:

--*/

#include "ast_counter.h"

void counter::update(unsigned el, int delta) {
    int & counter = get(el);
    counter += delta;
}

int & counter::get(unsigned el) {
    return m_data.insert_if_not_there2(el, 0)->get_data().m_value;
}

counter & counter::count(unsigned sz, const unsigned * els, int delta) {
    for(unsigned i=0; i<sz; i++) {
        update(els[i], delta);
    }
    return *this;
}

unsigned counter::get_positive_count() const {
    unsigned cnt = 0;
    iterator eit = begin();
    iterator eend = end();
    for(; eit!=eend; ++eit) {
        if( eit->m_value>0 ) { 
            cnt++;
        }
    }
    return cnt;
}

void counter::collect_positive(uint_set & acc) const {
    iterator eit = begin();
    iterator eend = end();
    for(; eit!=eend; ++eit) {
        if(eit->m_value>0) { acc.insert(eit->m_key); }
    }
}

bool counter::get_max_positive(unsigned & res) const {
    bool found = false;
    iterator eit = begin();
    iterator eend = end();
    for(; eit!=eend; ++eit) {
        if( eit->m_value>0 && (!found || eit->m_key>res) ) { 
            found = true;
            res = eit->m_key;
        }
    }
    return found;
}

unsigned counter::get_max_positive() const {
    unsigned max_pos;
    VERIFY(get_max_positive(max_pos));
    return max_pos;
}

int counter::get_max_counter_value() const {
    int res = 0;
    iterator eit = begin();
    iterator eend = end();
    for (; eit!=eend; ++eit) {
        if( eit->m_value>res ) { 
            res = eit->m_value;
        }
    }
    return res;
}

void var_counter::count_vars(const app * pred, int coef) {
    unsigned n = pred->get_num_args();
    for (unsigned i = 0; i < n; i++) {
        m_fv(pred->get_arg(i));
        for (unsigned j = 0; j < m_fv.size(); ++j) {
            if (m_fv[j]) {
                update(j, coef);
            }
        }
    }
    m_fv.reset();
}


unsigned var_counter::get_max_var(bool& has_var) {
    has_var = false;
    unsigned max_var = 0;
    ptr_vector<quantifier> qs;
    while (!m_todo.empty()) {
        expr* e = m_todo.back();
        m_todo.pop_back();
        if (m_visited.is_marked(e)) {
            continue;
        }
        m_visited.mark(e, true);
        switch(e->get_kind()) {
        case AST_QUANTIFIER: {
            qs.push_back(to_quantifier(e));
            break;                 
        }
        case AST_VAR: {
            if (to_var(e)->get_idx() >= max_var) {
                has_var = true;
                max_var = to_var(e)->get_idx();
            }
            break;
        }
        case AST_APP: {
            app* a = to_app(e);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                m_todo.push_back(a->get_arg(i));
            }
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }
    m_visited.reset();

    while (!qs.empty()) {
        var_counter aux_counter;
        quantifier* q = qs.back();
        qs.pop_back();
        aux_counter.m_todo.push_back(q->get_expr());
        bool has_var1 = false;
        unsigned max_v = aux_counter.get_max_var(has_var1);
        if (max_v >= max_var + q->get_num_decls()) {
            max_var = max_v - q->get_num_decls();
            has_var = has_var || has_var1;                
        }
    }

    return max_var;
}


unsigned var_counter::get_max_var(expr* e) {
    bool has_var = false;
    m_todo.push_back(e);
    return get_max_var(has_var);
}

unsigned var_counter::get_next_var(expr* e) {
    bool has_var = false;
    m_todo.push_back(e);
    unsigned mv = get_max_var(has_var);
    if (has_var) mv++;
    return mv;
}

