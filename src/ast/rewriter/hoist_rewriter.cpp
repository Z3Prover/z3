/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    hoist_rewriter.cpp

Abstract:

    Hoist predicates over disjunctions

Author:

    Nikolaj Bjorner (nbjorner) 2019-2-4

--*/


#include "ast/rewriter/hoist_rewriter.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

hoist_rewriter::hoist_rewriter(ast_manager & m, params_ref const & p):
    m(m), m_args1(m), m_args2(m), m_refs(m), m_subst(m) { 
    updt_params(p); 
}

expr_ref hoist_rewriter::mk_and(expr_ref_vector const& args) {
    if (m_elim_and) {
        expr_ref_vector negs(m);
        for (expr* a : args)
            if (m.is_false(a))
                return expr_ref(m.mk_false(), m);
            else if (m.is_true(a))
                continue;
            else
                negs.push_back(::mk_not(m, a));
        return ::mk_not(mk_or(negs));
    }
    else
        return ::mk_and(args);
}

expr_ref hoist_rewriter::mk_or(expr_ref_vector const& args) {
    return ::mk_or(args);
}

br_status hoist_rewriter::mk_or(unsigned num_args, expr * const * es, expr_ref & result) {
    if (num_args < 2) 
        return BR_FAILED;

    for (unsigned i = 0; i < num_args; ++i) 
        if (!is_and(es[i], nullptr)) 
            return BR_FAILED;

    bool turn = false;
    m_preds1.reset(); 
    m_preds2.reset();
    m_uf1.reset(); 
    m_uf2.reset();
    m_expr2var.reset();
    m_var2expr.reset();
    basic_union_find* uf[2] = { &m_uf1, &m_uf2 };
    obj_hashtable<expr>* preds[2] = { &m_preds1, &m_preds2 };
    expr_ref_vector* args[2] = { &m_args1, &m_args2 };
    VERIFY(is_and(es[0], args[turn]));
    expr* e1, *e2;
    for (expr* e : *(args[turn])) {
        if (m.is_eq(e, e1, e2))             
            (*uf)[turn].merge(mk_var(e1), mk_var(e2));
        else 
            (*preds)[turn].insert(e);
    }
    unsigned round = 0;
    for (unsigned j = 1; j < num_args; ++j) {
        ++round;
        m_es.reset();
        m_mark.reset();

        bool last = turn;
        turn = !turn;
        (*preds)[turn].reset();
        reset(m_uf0);
        VERIFY(is_and(es[j], args[turn]));

        for (expr* e : *args[turn]) {
            if (m.is_eq(e, e1, e2)) {
                m_es.push_back(e1);                
                m_uf0.merge(mk_var(e1), mk_var(e2));
            }    
            else if ((*preds)[last].contains(e)) 
                (*preds)[turn].insert(e);
        }

        if ((*preds)[turn].empty() && m_es.empty()) 
            return BR_FAILED;

        m_eqs.reset();
        for (expr* e : m_es) {
            if (m_mark.is_marked(e)) 
                continue;
            unsigned u = mk_var(e);
            unsigned v = u;
            m_roots.reset();
            do {
                m_mark.mark(e);
                unsigned r = (*uf)[last].find(v);
                if (m_roots.find(r, e2)) 
                    m_eqs.push_back({e, e2});
                else 
                    m_roots.insert(r, e);
                v = m_uf0.next(v);
                e = mk_expr(v);
            }
            while (u != v);
        }
        reset((*uf)[turn]);
        for (auto const& [e1, e2] : m_eqs) 
            (*uf)[turn].merge(mk_var(e1), mk_var(e2));
        if ((*preds)[turn].empty() && m_eqs.empty()) 
            return BR_FAILED;
    }
    if (m_eqs.empty()) {
        result = hoist_predicates((*preds)[turn], num_args, es);
        return BR_DONE;
    }
    // p & eqs & (or fmls)
    expr_ref_vector fmls(m);
    m_subst.reset();
    for (expr * p : (*preds)[turn]) {
        expr* q = nullptr;
        if (m.is_not(p, q)) 
            m_subst.insert(q, m.mk_false());
        else 
            m_subst.insert(p, m.mk_true());
        fmls.push_back(p);
    }
    for (auto& p : m_eqs) {
        if (m.is_value(p.first))
            std::swap(p.first, p.second);
        m_subst.insert(p.first, p.second);
        fmls.push_back(m.mk_eq(p.first, p.second));
    }    
    expr_ref ors(::mk_or(m, num_args, es), m);
    m_subst(ors);
    fmls.push_back(ors);
    result = mk_and(fmls);
    TRACE("hoist", tout << ors << " => " << result << "\n";);
    return BR_DONE;
}

unsigned hoist_rewriter::mk_var(expr* e) {
    unsigned v = 0;
    if (m_expr2var.find(e, v)) 
        return v;
    m_uf1.mk_var();
    v = m_uf2.mk_var();
    SASSERT(v == m_var2expr.size());
    m_expr2var.insert(e, v);
    m_var2expr.push_back(e);
    return v;
}

expr_ref hoist_rewriter::hoist_predicates(obj_hashtable<expr> const& preds, unsigned num_args, expr* const* es) {
    expr_ref_vector args(m), args1(m), fmls(m);
    for (unsigned i = 0; i < num_args; ++i) {
        VERIFY(is_and(es[i], &args1));
        fmls.reset();
        for (expr* e : args1) 
            if (!preds.contains(e))
                fmls.push_back(e);
        args.push_back(mk_and(fmls));
    }
    fmls.reset();
    fmls.push_back(mk_or(args));
    for (auto* p : preds) 
        fmls.push_back(p);
    return mk_and(fmls);
}


br_status hoist_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    switch (f->get_decl_kind()) {
    case OP_OR:        
        return mk_or(num_args, args, result);
    default:
        return BR_FAILED;
    }
}

bool hoist_rewriter::is_and(expr * e, expr_ref_vector* args) {
#if 0
    if (!args) 
        return m.is_and(e) || (m.is_not(e, e) && m.is_or(e));
    expr_fast_mark1 visited;
    args->reset();
    args->push_back(e);
    m_refs.reset();
    for (unsigned i = 0; i < args->size(); ++i) {
        e = args->get(i);
        if (visited.is_marked(e)) 
            goto drop;
        m_refs.push_back(e);
        visited.mark(e, true);
        if (m.is_and(e)) 
            args->append(to_app(e)->get_num_args(), to_app(e)->get_args());
        else if (m.is_not(e, e) && m.is_or(e)) 
            for (expr* arg : *to_app(e)) 
                args->push_back(::mk_not(m, arg));
        else 
            continue;
    drop:
        (*args)[i] = args->back();
        args->pop_back();
        --i;
    }
    return args->size() > 1;
#else
    if (m.is_and(e)) {
        if (args) {
            args->reset();
            args->append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
        return true;
    }
    if (m.is_not(e, e) && m.is_or(e)) {
        if (args) {
            args->reset();
            for (expr* arg : *to_app(e)) 
                args->push_back(::mk_not(m, arg));
            TRACE("hoist", tout << args << " " <<  * args << "\n");
        }
        return true;
    }
#endif
    return false;
}


void hoist_rewriter::reset(basic_union_find& uf) {
    uf.reset();
    for (expr* e : m_var2expr) {
        (void)e;
        uf.mk_var();
    }
}
