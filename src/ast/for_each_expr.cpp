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

subterms::subterms(expr_ref_vector const& es): m_es(es) {}
subterms::subterms(expr_ref& e) : m_es(e.m()) { m_es.push_back(e); }
subterms::iterator subterms::begin() { return iterator(*this, true); }
subterms::iterator subterms::end() { return iterator(*this, false); }
subterms::iterator::iterator(subterms& f, bool start): m_es(f.m_es) {
    if (!start) m_es.reset();
}
expr* subterms::iterator::operator*() {
    return m_es.back();
}
subterms::iterator subterms::iterator::operator++(int) {
    iterator tmp = *this;
    ++*this;
    return tmp;
}
subterms::iterator& subterms::iterator::operator++() {
    expr* e = m_es.back();
    m_visited.mark(e, true);
    if (is_app(e)) {
        for (expr* arg : *to_app(e)) {
            m_es.push_back(arg);
        }
    }
    while (!m_es.empty() && m_visited.is_marked(m_es.back())) {
        m_es.pop_back();
    }
    return *this;
}

bool subterms::iterator::operator==(iterator const& other) const {
    // ignore state of visited
    if (other.m_es.size() != m_es.size()) {
        return false;
    }
    for (unsigned i = m_es.size(); i-- > 0; ) {
        if (m_es.get(i) != other.m_es.get(i))
            return false;
    }
    return true;
}

bool subterms::iterator::operator!=(iterator const& other) const {
    return !(*this == other);
}

