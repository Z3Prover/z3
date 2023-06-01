/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    dependent_expr_state.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.
    
--*/

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/for_each_ast.h"

unsigned dependent_expr_state::num_exprs() {
    expr_fast_mark1 visited;
    unsigned r = 0;
    for (unsigned i = 0; i < qtail(); i++) 
        r += get_num_exprs((*this)[i].fml(), visited);
    return r;
}

void dependent_expr_state::freeze(func_decl* f) {
    if (m_frozen.is_marked(f) || !is_uninterp(f))
        return;
    m_frozen_trail.push_back(f);
    m_frozen.mark(f, true);
}

void dependent_expr_state::freeze(expr* term) {
    if (is_app(term) && to_app(term)->get_num_args() == 0)
        freeze(to_app(term)->get_decl());
    else {
        ast_mark visited;
        freeze_terms(term, false, visited);
    }
    
}

/**
* Freeze functions appearing as sub-expressions of 'e'.
* The only_as_array flag indicates whether to only freeze occurrences of as-array
* from elimination.
*/
void dependent_expr_state::freeze_terms(expr* e, bool only_as_array, ast_mark& visited) {
    auto& m = m_frozen_trail.get_manager();
    struct proc {
        bool only_as_array;
        array_util a;
        dependent_expr_state& st;
        proc(ast_manager& m, bool o, dependent_expr_state& d) :
            only_as_array(o), a(m), st(d) {}
        void operator()(func_decl* f) {
            if (!only_as_array)
                st.freeze(f);
            if (a.is_as_array(f, f) && is_uninterp(f))
                st.freeze(f);
        }
        void operator()(ast* s) {}
    };
    proc proc(m, only_as_array, *this);
    for_each_ast(proc, visited, e);
}

/**
* Freeze all functions used in recursive definitions
*/

void dependent_expr_state::freeze_recfun() {
    auto& m = m_frozen_trail.get_manager();
    recfun::util rec(m);
    if (!rec.has_rec_defs())
        return;
    unsigned sz = rec.get_rec_funs().size();
    if (m_num_recfun >= sz)
        return;
    
    ast_mark visited;
    for (func_decl* f : rec.get_rec_funs()) {
        auto& d = rec.get_def(f);
        if (!d.is_macro() && d.get_rhs())
            freeze_terms(d.get_rhs(), false, visited);
    }
    m_trail.push(value_trail(m_num_recfun));
    m_num_recfun = sz;
}

/**
* Freeze all functions used in lambda defined declarations
*/
void dependent_expr_state::freeze_lambda() {
    auto& m = m_frozen_trail.get_manager();
    unsigned sz = m.lambda_defs().size();
    if (m_num_lambdas >= sz)
        return;

    ast_mark visited;
    for (auto const& [f, body] : m.lambda_defs()) 
        freeze_terms(body, false, visited);
    m_trail.push(value_trail(m_num_lambdas));
    m_num_lambdas = sz;
}


/**
* The current qhead is to be updated to qtail. 
* Before this update, freeze all functions appearing in formulas.
*/
void dependent_expr_state::freeze_prefix() {
    ast_mark visited;
    for (unsigned i = qhead(); i < qtail(); ++i) 
        freeze_terms((*this)[i].fml(), false, visited);
}

/**
* Freeze functions in the unprocessed suffix that appear in dependencies and in as-array.
*/
void dependent_expr_state::freeze_suffix() {
    if (m_suffix_frozen)
        return;
    m_suffix_frozen = true;
    freeze_recfun();
    freeze_lambda();
    auto& m = m_frozen_trail.get_manager();
    ast_mark visited;
    ptr_vector<expr> es;
    for (unsigned i = qhead(); i < qtail(); ++i) {
        auto d = (*this)[i];
        if (d.dep()) {
            es.reset();
            m.linearize(d.dep(), es);
            for (expr* e : es)
                freeze_terms(e, false, visited);
        }
        freeze_terms(d.fml(), true, visited);
    }
}

bool dependent_expr_state::has_quantifiers() {
    if (m_has_quantifiers != l_undef)
        return m_has_quantifiers == l_true;
    bool found = false;
    for (unsigned i = qhead(); i < qtail(); ++i) 
        found |= ::has_quantifiers((*this)[i].fml());
    m_has_quantifiers = found ? l_true : l_false;
    return m_has_quantifiers == l_true;
}
