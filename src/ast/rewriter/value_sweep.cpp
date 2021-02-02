/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

    value_sweep.cpp

  Author:

    Nikolaj Bjorner 2020-04-25

--*/

#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/value_sweep.h"

value_sweep::value_sweep(ast_manager& m):
    m(m),
    m_gen(m),
    m_rec(m),
    m_dt(m),
    m_rewrite(m),
    m_values(m),
    m_args(m),
    m_pinned(m),
    m_rounds(10),
    m_range(20),
    m_qhead(0)
{}

void value_sweep::set_value_core(expr* e, expr* v) {
    m_values.reserve(e->get_id() + 1);
    m_values[e->get_id()] = v;
}

void value_sweep::set_value(expr* e, expr* v) {
    if (!is_reducible(e) || m_dt.is_accessor(e)) {
        set_value_core(e, v);
        m_pinned.push_back(e);
    }
}

void value_sweep::reset_values() {
    m_values.reset();
    m_pinned.reset();
}

expr* value_sweep::get_value(expr* e) const {
    if (m.is_value(e))
        return e;
    if (m_values.size() <= e->get_id())
        return nullptr;
    return m_values[e->get_id()];
}

void value_sweep::unassign(unsigned sz) {
    for (unsigned i = m_queue.size(); i-- > sz; ) {
        expr* e = m_queue[i];
        m_values[e->get_id()] = nullptr;
    }
    m_queue.shrink(sz);
    m_qhead = sz;
}

bool value_sweep::assign_next_value() {
    for (; m_vhead < m_vars.size(); ) {
        expr* v = m_vars[m_vhead];
        ++m_vhead;
        if (!get_value(v)) {
            unsigned index = m_rand() % m_range;
            expr_ref val = m_gen.get_value(v->get_sort(), index);
            set_value_core(v, val);
            m_queue.push_back(v);
            return true;
        }
    }
    return false;
}

bool value_sweep::is_reducible(expr* e) const {
    if (!is_app(e))
        return false;
    app* a = to_app(e);
    return 
        m_rec.is_defined(a) ||
        a->get_family_id() == m_dt.get_family_id() ||
        a->get_family_id() == m.get_basic_family_id();    
}

bool value_sweep::all_args_have_values(app* p) const {
    for (expr* arg : *p) {
        if (!get_value(arg))
            return false;
    }
    return true;
}

void value_sweep::propagate_values() {
    for (; m_qhead < m_queue.size(); ++m_qhead) {
        expr* e = m_queue[m_qhead];
        for (app* p : m_parents[e->get_id()]) {
            if (get_value(p))
                continue;
            if (!is_reducible(p))
                continue;
            if (!all_args_have_values(p))
                continue;            
            m_args.reset();
            for (expr* arg : *p) 
                m_args.push_back(get_value(arg));                                
            expr_ref new_value(m.mk_app(p->get_decl(), m_args), m);
            m_rewrite(new_value);
            TRACE("value_sweep", tout << "propagate " << mk_pp(p, m) << " " << new_value << "\n";);
            set_value_core(p, new_value);
            m_queue.push_back(p);
        }
    }
}

void value_sweep::init(expr_ref_vector const& terms) { 
    m_parents.reset();
    m_queue.reset();
    m_vars.reset();
    m_qhead = 0;
    m_vhead = 0;
    for (expr* t : subterms(terms)) {
        m_parents.reserve(t->get_id() + 1);
        if (get_value(t)) 
            m_queue.push_back(t);
        else if (!is_reducible(t))
            m_vars.push_back(t);
    }
    for (expr* t : subterms(terms)) {
        if (!is_app(t)) 
            continue;
        for (expr* arg : *to_app(t)) {
            m_parents[arg->get_id()].push_back(to_app(t));
        }
    }
}

void value_sweep::operator()(expr_ref_vector const& terms,
                             vector<expr_ref_vector>& values) {

    unsigned qhead0 = m_queue.size();
    init(terms);
    propagate_values();
    unsigned qhead = m_queue.size();
    for (unsigned i = 0; i < m_rounds; ++i) {
        m_vhead = 0;
        while (assign_next_value()) {
            propagate_values();
        }
        expr_ref_vector vec(m);
        for (expr* t : terms) {
            vec.push_back(get_value(t));
        }
        values.push_back(vec);
        unassign(qhead);
    }
    unassign(qhead0); 
}
