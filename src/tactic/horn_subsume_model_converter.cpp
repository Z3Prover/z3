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


#include "tactic/horn_subsume_model_converter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"
#include "model/model_smt2_pp.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/for_each_expr.h"
#include "ast/well_sorted.h"

void horn_subsume_model_converter::insert(app* head, expr* body) {
    m_delay_head.push_back(head);
    m_delay_body.push_back(body);
}

void horn_subsume_model_converter::insert(app* head, unsigned sz, expr* const* body) {
    expr_ref b(m);
    bool_rewriter(m).mk_and(sz, body, b);
    insert(head, b.get());
}


bool horn_subsume_model_converter::mk_horn(
    app* head, expr* body, func_decl_ref& pred, expr_ref& body_res) {

    expr_ref_vector conjs(m), subst(m);
    ptr_vector<sort> sorts2;
    var_subst vs(m, false);

    if (!is_uninterp(head)) {
        return false;
    }

    pred = head->get_decl();
    unsigned arity = head->get_num_args();
    
    expr_free_vars fv;
    fv(head);
    fv.accumulate(body);
    
    if (arity == 0 && fv.empty()) {
        body_res = body;
        return true;
    }
    fv.set_default_sort(m.mk_bool_sort());

    svector<symbol> names;
    for (unsigned i = 0; i < fv.size(); ++i) {
        names.push_back(symbol(i));
    }
    names.reverse();
    fv.reverse();
    conjs.push_back(body);
    for (unsigned i = 0; i < arity; ++i) {
        expr* arg = head->get_arg(i);
        var_ref v(m);
        v = m.mk_var(fv.size()+i, arg->get_sort());
        
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
    body_expr = m.mk_and(conjs.size(), conjs.data());

    // substitute variables directly.
    if (!subst.empty()) {
        body_expr = vs(body_expr, subst.size(), subst.data());
    }    

    if (fv.empty()) {
        SASSERT(subst.empty());
        body_res = body_expr;
    }   
    else {
        body_res  = m.mk_exists(fv.size(), fv.data(), names.data(), body_expr.get()); 
        m_rewrite(body_res);
        
    }
    TRACE("mc",
          tout << mk_pp(head, m) << " :- " << mk_pp(body, m) << "\n";
          tout << pred->get_name() << " :- " << mk_pp(body_res.get(), m) << "\n";);

    return true;
}


bool horn_subsume_model_converter::mk_horn(
    expr* clause, func_decl_ref& pred, expr_ref& body) {

    // formula is closed.
    DEBUG_CODE(expr_free_vars fv; fv(clause); SASSERT(fv.empty()););
        
    while (is_quantifier(clause) && to_quantifier(clause)->get_kind() == forall_k) {
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

void horn_subsume_model_converter::add_default_proc::operator()(app* n) {

    //
    // predicates that have not been assigned values 
    // in the Horn model are assumed false.
    //
    if (m.is_bool(n) && 
        !m_md->has_interpretation(n->get_decl()) &&
        (n->get_family_id() == null_family_id)) {
        TRACE("mc", tout << "adding: " << n->get_decl()->get_name() << "\n";);
        if (n->get_decl()->get_arity() == 0) {
            m_md->register_decl(n->get_decl(), m.mk_false());
        }
        else { 
            func_interp* fi = alloc(func_interp, m, n->get_decl()->get_arity());
            fi->set_else(m.mk_false());
            m_md->register_decl(n->get_decl(), fi);            
        }
    }
}

void horn_subsume_model_converter::add_default_false_interpretation(expr* e, model_ref& md) {
    add_default_proc proc(m, md);
    for_each_expr(proc, e);
}


void horn_subsume_model_converter::operator()(expr_ref& fml) {
    NOT_IMPLEMENTED_YET();
}

void horn_subsume_model_converter::operator()(model_ref& mr) {

    func_decl_ref pred(m);
    expr_ref      body_res(m);
    for (unsigned i = 0; i < m_delay_head.size(); ++i) {
        VERIFY(mk_horn(m_delay_head[i].get(), m_delay_body[i].get(), pred, body_res));
        insert(pred.get(), body_res.get());
    }
    m_delay_head.reset();
    m_delay_body.reset();

    TRACE("mc", tout << m_funcs.size() << "\n"; model_smt2_pp(tout, m, *mr, 0););
    for (unsigned i = m_funcs.size(); i > 0; ) {
        --i;
        func_decl* h = m_funcs[i].get();
        expr_ref body(m_bodies[i].get(), m);
        unsigned arity = h->get_arity();
        add_default_false_interpretation(body, mr);
        SASSERT(m.is_bool(body));
                
        TRACE("mc", tout << "eval: " << h->get_name() << "\n" << body << "\n";);
        body = (*mr)(body);
        
        TRACE("mc", tout << "to:\n" << body << "\n";);
                
        if (arity == 0) {
            expr* e = mr->get_const_interp(h);
            if (e) {
                body = m.mk_or(e, body);
            }
            m_rewrite(body);
            mr->register_decl(h, body);
        }
        else {
            func_interp* f = mr->get_func_interp(h);
            if (f) {
                expr* e = f->get_else();
                body = m.mk_or(e, body);
            }
            else {
                f = alloc(func_interp, m, arity);
                mr->register_decl(h, f);
            }
            m_rewrite(body);
            f->set_else(body);
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

