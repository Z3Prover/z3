/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    for_each_expr.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-28.

Revision History:

--*/

#include "ast/for_each_expr.h"

struct expr_counter_proc {
    unsigned m_num;
    expr_counter_proc():m_num(0) {}
    void operator()(var * n)        { m_num++; }
    void operator()(app * n)        { m_num++; if (n->get_decl()->is_associative()) m_num += n->get_num_args() - 2; }
    void operator()(quantifier * n) { m_num++; }
};

unsigned get_num_exprs(expr * n, expr_mark & visited) {
    expr_counter_proc counter;
    for_each_expr(counter, visited, n);
    return counter.m_num;
}

unsigned get_num_exprs(expr * n, expr_fast_mark1 & visited) {
    expr_counter_proc counter;
    for_each_expr_core<expr_counter_proc, expr_fast_mark1, false, false>(counter, visited, n);
    return counter.m_num;
}

unsigned get_num_exprs(expr * n) {
    expr_fast_mark1 visited;
    return get_num_exprs(n, visited);
}


void get_num_internal_exprs(unsigned_vector& counts, ptr_vector<expr>& todo, expr * n) {
    counts.reserve(n->get_id() + 1);
    unsigned& rc = counts[n->get_id()];
    if (rc > 0) {
        --rc;
        return;
    }
    rc = n->get_ref_count() - 1;
    unsigned i = todo.size();
    todo.push_back(n);
    for (; i < todo.size(); ++i) {
        n = todo[i];
        if (!is_app(n))
            continue;
        for (expr* arg : *to_app(n)) {
            unsigned id = arg->get_id();
            counts.reserve(id + 1);
            unsigned& rc = counts[id];
            if (rc > 0) {
                --rc;
                continue;
            }
            rc = arg->get_ref_count() - 1;
            todo.push_back(arg);
        }
    }
}

unsigned count_internal_nodes(unsigned_vector& counts, ptr_vector<expr>& todo) {
    unsigned internal_nodes = 0;
    for (expr* t : todo) {
        if (counts[t->get_id()] == 0)
            ++internal_nodes;
        else
            counts[t->get_id()] = 0;
    }
    todo.reset();
    return internal_nodes;
    
}


namespace has_skolem_functions_ns {
    struct found {};
    struct proc {
        void operator()(var * n) const {}
        void operator()(app const * n) const { if (n->get_decl()->is_skolem() && n->get_num_args() > 0) throw found(); }
        void operator()(quantifier * n) const {}
    };
};

bool has_skolem_functions(expr * n) {
    has_skolem_functions_ns::proc p;
    try {
        for_each_expr(p, n);
    }
    catch (const has_skolem_functions_ns::found &) {
        return true;
    }
    return false;
}

subterms::subterms(expr_ref_vector const& es, bool include_bound, ptr_vector<expr>* esp, expr_mark* vp): m_include_bound(include_bound), m_es(es), m_esp(esp), m_vp(vp) {}
subterms::subterms(expr_ref const& e, bool include_bound, ptr_vector<expr>* esp, expr_mark* vp) : m_include_bound(include_bound), m_es(e.m()), m_esp(esp), m_vp(vp) { if (e) m_es.push_back(e); }
subterms::iterator subterms::begin() const { return iterator(* this, m_esp, m_vp, true); }
subterms::iterator subterms::end() const { return iterator(*this, nullptr, nullptr, false); }
subterms::iterator::iterator(subterms const& f, ptr_vector<expr>* esp, expr_mark* vp, bool start): m_include_bound(f.m_include_bound), m_esp(esp), m_visitedp(vp) {
    if (!esp)
        m_esp = &m_es;
    else
        m_esp->reset();
    if (!m_visitedp)
        m_visitedp = &m_visited;
    if (start)
        m_esp->append(f.m_es.size(), f.m_es.data());
}
expr* subterms::iterator::operator*() {
    return m_esp->back();
}
subterms::iterator subterms::iterator::operator++(int) {
    iterator tmp = *this;
    ++*this;
    return tmp;
}
subterms::iterator& subterms::iterator::operator++() {
    expr* e = m_esp->back();
    // IF_VERBOSE(0, verbose_stream() << e->get_ref_count() << "\n");
    SASSERT(e->get_ref_count() > 0);
    m_visitedp->mark(e, true);
    if (is_app(e)) 
        for (expr* arg : *to_app(e)) 
            m_esp->push_back(arg);            
    else if (is_quantifier(e) && m_include_bound)
        m_esp->push_back(to_quantifier(e)->get_expr());

    while (!m_esp->empty() && m_visitedp->is_marked(m_esp->back())) 
        m_esp->pop_back();
    
    return *this;
}

bool subterms::iterator::operator!=(iterator const& other) const {
    // ignore state of visited
    if (other.m_esp->size() != m_esp->size()) {
        return true;
    }
    for (unsigned i = m_esp->size(); i-- > 0; ) {
        if (m_esp->get(i) != other.m_esp->get(i))
            return true;
    }
    return false;
}


subterms_postorder::subterms_postorder(expr_ref_vector const& es, bool include_bound): m_include_bound(include_bound), m_es(es) {}
subterms_postorder::subterms_postorder(expr_ref const& e, bool include_bound) : m_include_bound(include_bound), m_es(e.m()) { if (e) m_es.push_back(e); }
subterms_postorder::iterator subterms_postorder::begin() { return iterator(*this, true); }
subterms_postorder::iterator subterms_postorder::end() { return iterator(*this, false); }
subterms_postorder::iterator::iterator(subterms_postorder& f, bool start): m_include_bound(f.m_include_bound), m_es(f.m_es) {
    if (!start) m_es.reset();
    next();
}
expr* subterms_postorder::iterator::operator*() {
    return m_es.back();
}
subterms_postorder::iterator subterms_postorder::iterator::operator++(int) {
    iterator tmp = *this;
    ++*this;
    return tmp;
}

void subterms_postorder::iterator::next() {
    while (!m_es.empty()) {
        expr* e = m_es.back();
        if (m_visited.is_marked(e)) {
            m_es.pop_back();
            continue;
        }
        bool all_visited = true;
        if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                if (!m_visited.is_marked(arg)) {
                    m_es.push_back(arg);
                    all_visited = false;
                }
            }
        }
        else if (is_quantifier(e) && m_include_bound) {
            expr* body = to_quantifier(e)->get_expr();
            if (!m_visited.is_marked(body)) {
                m_es.push_back(body);
                all_visited = false;
            }
        }
        if (all_visited) {
            m_visited.mark(e, true);
            break;
        }
    }

}

subterms_postorder::iterator& subterms_postorder::iterator::operator++() {
    next();
    return *this;
}

bool subterms_postorder::iterator::operator!=(iterator const& other) const {
    // ignore state of visited
    if (other.m_es.size() != m_es.size()) {
        return true;
    }
    for (unsigned i = m_es.size(); i-- > 0; ) {
        if (m_es.get(i) != other.m_es.get(i))
            return true;
    }
    return false;
}
