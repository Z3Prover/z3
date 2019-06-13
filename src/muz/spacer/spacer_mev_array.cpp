/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_mev_array.cpp

Abstract:

    Evaluate array expressions in a given model.

Author:

Revision History:

--*/
#include"model/model.h"
#include "model/model_evaluator_params.hpp"
#include"ast/rewriter/rewriter_types.h"
#include"model/model_evaluator.h"
#include"muz/spacer/spacer_mev_array.h"
#include"ast/rewriter/bool_rewriter.h"
#include"ast/rewriter/arith_rewriter.h"
#include"ast/rewriter/bv_rewriter.h"
#include"ast/rewriter/datatype_rewriter.h"
#include"ast/rewriter/array_rewriter.h"
#include"ast/rewriter/rewriter_def.h"
#include"ast/ast_pp.h"
#include"model/func_interp.h"



// model_evaluator_array_util


void model_evaluator_array_util::eval_exprs(model& mdl, expr_ref_vector& es) {
    for (unsigned j = 0; j < es.size(); ++j) {
        if (m_array.is_as_array(es.get (j))) {
            expr_ref r (m);
            eval(mdl, es.get (j), r);
            es.set (j, r);
        }
    }
}

bool model_evaluator_array_util::extract_array_func_interp(model& mdl, expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case) {
    SASSERT(m_array.is_array(a));

    TRACE("model_evaluator", tout << mk_pp(a, m) << "\n";);
    while (m_array.is_store(a)) {
        expr_ref_vector store(m);
        store.append(to_app(a)->get_num_args()-1, to_app(a)->get_args()+1);
        eval_exprs(mdl, store);
        stores.push_back(store);
        a = to_app(a)->get_arg(0);
    }

    if (m_array.is_const(a)) {
        else_case = to_app(a)->get_arg(0);
        return true;
    }

    while (m_array.is_as_array(a)) {
        func_decl* f = m_array.get_as_array_func_decl(to_app(a));
        func_interp* g = mdl.get_func_interp(f);
        unsigned sz = g->num_entries();
        unsigned arity = f->get_arity();
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref_vector store(m);
            func_entry const* fe = g->get_entry(i);
            store.append(arity, fe->get_args());
            store.push_back(fe->get_result());
            for (unsigned j = 0; j < store.size(); ++j) {
                if (!is_ground(store[j].get())) {
                    TRACE("model_evaluator", tout << "could not extract array interpretation: " << mk_pp(a, m) << "\n" << mk_pp(store[j].get(), m) << "\n";);
                    return false;
                }
            }
            eval_exprs(mdl, store);
            stores.push_back(store);
        }
        else_case = g->get_else();
        if (!else_case) {
            TRACE("model_evaluator", tout << "no else case " << mk_pp(a, m) << "\n";);
            return false;
        }
        if (!is_ground(else_case)) {
            TRACE("model_evaluator", tout << "non-ground else case " << mk_pp(a, m) << "\n" << mk_pp(else_case, m) << "\n";);
            return false;
        }
        if (m_array.is_as_array(else_case)) {
            expr_ref r (m);
            eval(mdl, else_case, r);
            else_case = r;
        }
        TRACE("model_evaluator", tout << "else case: " << mk_pp(else_case, m) << "\n";);
        return true;
    }
    TRACE("model_evaluator", tout << "no translation: " << mk_pp(a, m) << "\n";);

    return false;
}

void model_evaluator_array_util::eval_array_eq(model& mdl, app* e, expr* arg1, expr* arg2, expr_ref& res) {
    TRACE("model_evaluator", tout << "array equality: " << mk_pp(e, m) << "\n";);
    expr_ref v1(m), v2(m);
    eval (mdl, arg1, v1);
    eval (mdl, arg2, v2);
    if (v1 == v2) {
        res = m.mk_true ();
        return;
    }
    sort* s = m.get_sort(arg1);
    sort* r = get_array_range(s);
    // give up evaluating finite domain/range arrays
    if (!r->is_infinite() && !r->is_very_big() && !s->is_infinite() && !s->is_very_big()) {
        TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
        res.reset ();
        return;
    }
    vector<expr_ref_vector> store;
    expr_ref else1(m), else2(m);
    if (!extract_array_func_interp(mdl, v1, store, else1) ||
            !extract_array_func_interp(mdl, v2, store, else2)) {
        TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
        res.reset ();
        return;
    }

    if (else1 != else2) {
        if (m.is_value(else1) && m.is_value(else2)) {
            TRACE("model_evaluator", tout
                    << "defaults are different: " << mk_pp(e, m) << " "
                    << mk_pp(else1, m) << " " << mk_pp(else2, m) << "\n";);
            res = m.mk_false ();
        }
        else if (m_array.is_array(else1)) {
            eval_array_eq(mdl, e, else1, else2, res);
        }
        else {
            TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            res.reset ();
        }
        return;
    }

    expr_ref s1(m), s2(m), w1(m), w2(m);
    expr_ref_vector args1(m), args2(m);
    args1.push_back(v1);
    args2.push_back(v2);
    for (unsigned i = 0; i < store.size(); ++i) {
        args1.resize(1);
        args2.resize(1);
        args1.append(store[i].size()-1, store[i].c_ptr());
        args2.append(store[i].size()-1, store[i].c_ptr());
        s1 = m_array.mk_select(args1.size(), args1.c_ptr());
        s2 = m_array.mk_select(args2.size(), args2.c_ptr());
        eval (mdl, s1, w1);
        eval (mdl, s2, w2);
        if (w1 == w2) {
            continue;
        }
        if (m.is_value(w1) && m.is_value(w2)) {
            TRACE("model_evaluator", tout << "Equality evaluation: " << mk_pp(e, m) << "\n";
                    tout << mk_pp(s1, m) << " |-> " << mk_pp(w1, m) << "\n";
                    tout << mk_pp(s2, m) << " |-> " << mk_pp(w2, m) << "\n";);
            res = m.mk_false ();
        }
        else if (m_array.is_array(w1)) {
            eval_array_eq(mdl, e, w1, w2, res);
            if (m.is_true (res)) {
                continue;
            }
        }
        else {
            TRACE("model_evaluator", tout << "equality is unknown: " << mk_pp(e, m) << "\n";);
            res.reset ();
        }
        return;
    }
    res = m.mk_true ();
}

void model_evaluator_array_util::eval(model& mdl, expr* e, expr_ref& r, bool model_completion) {
    model_evaluator mev (mdl);
    mev.set_model_completion (model_completion);
    bool eval_result = true;
    try {
        mev (e, r);
    }
    catch (model_evaluator_exception &) {
        eval_result = false;
    }
    VERIFY(eval_result);

    if (m_array.is_array(e)) {
        vector<expr_ref_vector> stores;
        expr_ref_vector args(m);
        expr_ref else_case(m);
        if (extract_array_func_interp(mdl, r, stores, else_case)) {
            r = m_array.mk_const_array(m.get_sort(e), else_case);
            while (!stores.empty() && stores.back().back() == else_case) {
                stores.pop_back();
            }
            for (unsigned i = stores.size(); i > 0; ) {
                --i;
                args.resize(1);
                args[0] = r;
                args.append(stores[i]);
                r = m_array.mk_store(args.size(), args.c_ptr());
            }
            return;
        }
    }
    return;
}
