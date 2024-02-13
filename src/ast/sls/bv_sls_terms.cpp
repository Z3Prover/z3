/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls.cpp

Abstract:

    A Stochastic Local Search (SLS) engine
    Uses invertibility conditions, 
    interval annotations
    don't care annotations

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/sls/bv_sls.h"

namespace bv {

    sls_terms::sls_terms(ast_manager& m): 
        m(m), 
        bv(m),
        m_assertions(m),
        m_pinned(m),
        m_translated(m), 
        m_terms(m){}


    void sls_terms::assert_expr(expr* e) {
        m_assertions.push_back(ensure_binary(e));
    }

    expr* sls_terms::ensure_binary(expr* e) {
        expr* top = e;
        m_pinned.push_back(e);
        m_todo.push_back(e);
        expr_fast_mark1 mark;
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            expr* e = m_todo[i];
            if (!is_app(e))
                continue;
            if (m_translated.get(e->get_id(), nullptr))
                continue;
            if (mark.is_marked(e))
                continue;
            mark.mark(e);
            for (auto arg : *to_app(e))
                m_todo.push_back(arg);
        }
        std::stable_sort(m_todo.begin(), m_todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
        for (expr* e : m_todo)
            ensure_binary_core(e);
        m_todo.reset();
        return m_translated.get(top->get_id());
    }

    void sls_terms::ensure_binary_core(expr* e) {
        app* a = to_app(e);
        auto arg = [&](unsigned i) {
            return m_translated.get(a->get_arg(i)->get_id());
        };
        unsigned num_args = a->get_num_args();
        expr_ref r(m);
#define FOLD_OP(oper)           \
        r = arg(0);             \
        for (unsigned i = 1; i < num_args; ++i)\
            r = oper(r, arg(i)); \

        if (m.is_and(e)) {
            FOLD_OP(m.mk_and);
        }
        else if (m.is_or(e)) {
            FOLD_OP(m.mk_or);
        }
        else if (m.is_xor(e)) {
            FOLD_OP(m.mk_xor);
        }
        else if (bv.is_bv_and(e)) {
            FOLD_OP(bv.mk_bv_and);
        }
        else if (bv.is_bv_or(e)) {
            FOLD_OP(bv.mk_bv_or);
        }
        else if (bv.is_bv_xor(e)) {
            FOLD_OP(bv.mk_bv_xor);
        }
        else if (bv.is_bv_add(e)) {
            FOLD_OP(bv.mk_bv_add);
        }
        else if (bv.is_bv_mul(e)) {
            FOLD_OP(bv.mk_bv_mul);
        }
        else if (bv.is_concat(e)) {
            FOLD_OP(bv.mk_concat);
        }
        else {
            for (unsigned i = 0; i < num_args; ++i)
                m_todo.push_back(arg(i));
            r = m.mk_app(a->get_decl(), num_args, m_todo.data());
            m_todo.reset();
        }
        m_translated.setx(e->get_id(), r);
    }


    void sls_terms::init() {
        // populate terms
        expr_fast_mark1 mark;
        for (expr* e : m_assertions)
            m_todo.push_back(e);
        while (!m_todo.empty()) {
            expr* e = m_todo.back();
            m_todo.pop_back();
            if (mark.is_marked(e) || !is_app(e))
                continue;
            mark.mark(e);            
            m_terms.setx(e->get_id(), to_app(e));
            for (expr* arg : *to_app(e))
                m_todo.push_back(arg);
        }       
        // populate parents
        m_parents.reserve(m_terms.size());
        for (expr* e : m_terms) {
            if (!e || !is_app(e))
                continue;
            for (expr* arg : *to_app(e))
                m_parents[arg->get_id()].push_back(e);                
        }
        for (auto a : m_assertions)
            m_assertion_set.insert(a->get_id());
    }

}
