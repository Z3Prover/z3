/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_subsume_model_converter.cpp

Abstract:

    Model converter for redundant Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-16

Revision History:

--*/


#include "horn_subsume_model_converter.h"
#include "var_subst.h"
#include "ast_pp.h"
#include "model_smt2_pp.h"
#include "bool_rewriter.h"

void horn_subsume_model_converter::insert(app* head, expr* body) {
    func_decl_ref pred(m);
    expr_ref      body_res(m);
    VERIFY(mk_horn(head, body, pred, body_res));
    insert(pred.get(), body_res.get());
}

void horn_subsume_model_converter::insert(app* head, unsigned sz, expr* const* body) {
    expr_ref b(m);
    bool_rewriter(m).mk_and(sz, body, b);
    insert(head, b.get());
}


bool horn_subsume_model_converter::mk_horn(
    app* head, expr* body, func_decl_ref& pred, expr_ref& body_res) const {

    expr_ref_vector conjs(m), subst(m);
    ptr_vector<sort> sorts, sorts2;
    var_subst vs(m, false);

    if (!is_uninterp(head)) {
        return false;
    }

    pred = head->get_decl();
    unsigned arity = head->get_num_args();
    
    get_free_vars(head, sorts);
    get_free_vars(body, sorts);
    
    if (arity == 0 && sorts.empty()) {
        body_res = body;
        return true;
    }

    svector<symbol> names;
    for (unsigned i = 0; i < sorts.size(); ++i) {
        if (!sorts[i]) {
            sorts[i] = m.mk_bool_sort();
        }            
        names.push_back(symbol(i));
    }
    names.reverse();
    sorts.reverse();
    conjs.push_back(body);
    for (unsigned i = 0; i < arity; ++i) {
        expr* arg = head->get_arg(i);
        var_ref v(m);
        v = m.mk_var(sorts.size()+i,m.get_sort(arg));
        
        if (is_var(arg)) {
            unsigned w = to_var(arg)->get_idx();
            if (w >= subst.size()) {
                subst.resize(w+1);
            }
            if (subst[w].get()) {
                conjs.push_back(m.mk_eq(v, subst[w].get()));
            }
            else {
                subst[w] = v;
            }
        }
        else {
            conjs.push_back(m.mk_eq(v, arg));
        }
    }
    expr_ref body_expr(m);
    body_expr = m.mk_and(conjs.size(), conjs.c_ptr());

    // substitute variables directly.
    if (!subst.empty()) {
        expr_ref tmp(body_expr);
        vs(tmp, subst.size(), subst.c_ptr(), body_expr);
    }    


    // remove bound variables that are redundant.
    get_free_vars(body_expr, sorts2);
    subst.reset();

    unsigned num_bound_vars = sorts.size();
    unsigned new_num_bound_vars = 0;

    for (unsigned i = 0, j = 0; i < sorts2.size(); ++i) {
        if (sorts2[i]) {
            subst.push_back(m.mk_var(j++, sorts2[i]));
            if (i < num_bound_vars) {
                ++new_num_bound_vars;
            }
        }
        else {
            subst.push_back(0);
        }
    }
    if (new_num_bound_vars < num_bound_vars) {
        expr_ref tmp(body_expr);
        vs(tmp, subst.size(), subst.c_ptr(), body_expr);        
        sorts.reset();
        names.reset();
        for (unsigned i = 0; i < num_bound_vars; ++i) {
            if (sorts2[i]) {
                sorts.push_back(sorts2[i]);
                names.push_back(symbol(sorts.size()));
            }
        }
        sorts.reverse();
        names.reverse();
    }
    if (sorts.empty()) {
        body_res = body_expr;
    }   
    else {
        body_res  = m.mk_exists(sorts.size(), sorts.c_ptr(), names.c_ptr(), body_expr.get()); 
    }
    TRACE("dl",
          tout << mk_pp(head, m) << " :- " << mk_pp(body, m) << "\n";
          tout << pred->get_name() << " :- " << mk_pp(body_res.get(), m) << "\n";);

    return true;
}


bool horn_subsume_model_converter::mk_horn(
    expr* clause, func_decl_ref& pred, expr_ref& body) const {
    ptr_vector<sort> sorts;

    // formula is closed.
    DEBUG_CODE(get_free_vars(clause, sorts); SASSERT(sorts.empty()););
        
    while (is_quantifier(clause) && to_quantifier(clause)->is_forall()) {
        quantifier* q = to_quantifier(clause);
        clause = q->get_expr();
    }
    expr* e1, *e2;
    if (m.is_implies(clause, e1, e2)) {        
        if (!is_uninterp(e2)) {
            return false;
        }
        return mk_horn(to_app(e2), e1, pred, body);
    }
    else if (m.is_or(clause)) {
        // todo?
        return false;        
    }
    else {
        return false;
    }
}


void horn_subsume_model_converter::operator()(model_ref& mr) {
    for (unsigned i = m_funcs.size(); i > 0; ) {
        --i;
        func_decl* h = m_funcs[i].get();
        expr_ref body(m_bodies[i].get(), m);
        unsigned arity = h->get_arity();
        
        expr_ref tmp(body);
        mr->eval(tmp, body);
        TRACE("dl", tout << "eval: " << mk_pp(tmp, m) << "\nto:\n" << mk_pp(body, m) << "\n";);
        TRACE("dl", model_smt2_pp(tout, m, *mr, 0););
        
        if (arity == 0) {
            expr* e = mr->get_const_interp(h);
            if (e) {
                mr->register_decl(h, m.mk_or(e, body));
            }
            else {
                mr->register_decl(h, body);
            }
        }
        else {
            func_interp* f = mr->get_func_interp(h);
            if (f) {
                f->set_else(m.mk_or(f->get_else(), body.get()));
            }
            else {
                f = alloc(func_interp, m, arity);
                f->set_else(body);
                mr->register_decl(h, f);
            }
        }
    }
}


model_converter* horn_subsume_model_converter::translate(ast_translation & translator) {
    horn_subsume_model_converter* mc = alloc(horn_subsume_model_converter, translator.to());
    for (unsigned i = 0; i < m_funcs.size(); ++i) {
        mc->insert(translator(m_funcs[i].get()), translator(m_bodies[i].get()));
    }
    return mc;
}

