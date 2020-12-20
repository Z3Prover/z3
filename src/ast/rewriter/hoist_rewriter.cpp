/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    hoist_rewriter.cpp

Abstract:

    Hoist predicates over disjunctions

Author:

    Nikolaj Bjorner (nbjorner) 2019-2-4

Notes:

--*/


#include "ast/rewriter/hoist_rewriter.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"


hoist_rewriter::hoist_rewriter(ast_manager & m, params_ref const & p):
    m_manager(m), m_args1(m), m_args2(m), m_subst(m) { 
    updt_params(p); 
}

br_status hoist_rewriter::mk_or(unsigned num_args, expr * const * es, expr_ref & result) {
    if (num_args < 2) {
        return BR_FAILED;
    }
    for (unsigned i = 0; i < num_args; ++i) {
        if (!is_and(es[i], nullptr)) {
            return BR_FAILED;
        }
    }

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
        if (m().is_eq(e, e1, e2)) {            
            (*uf)[turn].merge(mk_var(e1), mk_var(e2));
        }
        else {
            (*preds)[turn].insert(e);
        }
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
            if (m().is_eq(e, e1, e2)) {
                m_es.push_back(e1);                
                m_uf0.merge(mk_var(e1), mk_var(e2));
            }    
            else if ((*preds)[last].contains(e)) {
                (*preds)[turn].insert(e);
            }
        }

        if ((*preds)[turn].empty() && m_es.empty()) {
            return BR_FAILED;
        }

        m_eqs.reset();
        for (expr* e : m_es) {
            if (m_mark.is_marked(e)) {
                continue;
            }
            unsigned u = mk_var(e);
            unsigned v = u;
            m_roots.reset();
            do {
                m_mark.mark(e);
                unsigned r = (*uf)[last].find(v);
                if (m_roots.find(r, e2)) {
                    m_eqs.push_back(std::make_pair(e, e2));
                }
                else {
                    m_roots.insert(r, e);
                }
                v = m_uf0.next(v);
                e = mk_expr(v);
            }
            while (u != v);
        }
        reset((*uf)[turn]);
        for (auto const& p : m_eqs) 
            (*uf)[turn].merge(mk_var(p.first), mk_var(p.second));
        if ((*preds)[turn].empty() && m_eqs.empty()) 
            return BR_FAILED;
    }
    if (m_eqs.empty()) {
        result = hoist_predicates((*preds)[turn], num_args, es);
        return BR_DONE;
    }
    // p & eqs & (or fmls)
    expr_ref_vector fmls(m());
    m_subst.reset();
    for (expr * p : (*preds)[turn]) {
        expr* q = nullptr;
        if (m().is_not(p, q)) {
            m_subst.insert(q, m().mk_false());
        }
        else {
            m_subst.insert(p, m().mk_true());
        }
        fmls.push_back(p);
    }
    for (auto& p : m_eqs) {
        if (m().is_value(p.first))
            std::swap(p.first, p.second);
        m_subst.insert(p.first, p.second);
        fmls.push_back(m().mk_eq(p.first, p.second));
    }    
    expr_ref ors(::mk_or(m(), num_args, es), m());
    m_subst(ors);
    fmls.push_back(ors);
    result = mk_and(fmls);
    TRACE("hoist", tout << ors << " => " << result << "\n";);
    return BR_DONE;
}

unsigned hoist_rewriter::mk_var(expr* e) {
    unsigned v = 0;
    if (m_expr2var.find(e, v)) {
        return v;
    }
    m_uf1.mk_var();
    v = m_uf2.mk_var();
    SASSERT(v == m_var2expr.size());
    m_expr2var.insert(e, v);
    m_var2expr.push_back(e);
    return v;
}

expr_ref hoist_rewriter::hoist_predicates(obj_hashtable<expr> const& preds, unsigned num_args, expr* const* es) {
    expr_ref result(m());
    expr_ref_vector args(m()), fmls(m());
    for (unsigned i = 0; i < num_args; ++i) {
        VERIFY(is_and(es[i], &m_args1));
        fmls.reset();
        for (expr* e : m_args1) {
            if (!preds.contains(e))
                fmls.push_back(e);
        }
        args.push_back(::mk_and(fmls));
    }
    fmls.reset();
    fmls.push_back(::mk_or(args));
    for (auto* p : preds) 
        fmls.push_back(p);
    result = ::mk_and(fmls);
    return result;
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
    if (m().is_and(e)) {
        if (args) {
            args->reset();
            args->append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
        return true;
    }
    if (m().is_not(e, e) && m().is_or(e)) {
        if (args) {
            args->reset();
            for (expr* arg : *to_app(e)) {
                args->push_back(::mk_not(m(), arg));
            }
        }
        return true;
    }
    return false;
}


void hoist_rewriter::reset(basic_union_find& uf) {
    uf.reset();
    for (expr* e : m_var2expr) {
        (void)e;
        uf.mk_var();
    }
}
