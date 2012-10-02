/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    macro_finder.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-05.

Revision History:

--*/

#include"macro_finder.h"
#include"occurs.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

bool macro_finder::is_macro(expr * n, app * & head, expr * & def) {
    if (!is_quantifier(n) || !to_quantifier(n)->is_forall())
        return false;
    TRACE("macro_finder", tout << "processing: " << mk_pp(n, m_manager) << "\n";);
    expr * body        = to_quantifier(n)->get_expr();
    unsigned num_decls = to_quantifier(n)->get_num_decls();
    return m_util.is_simple_macro(body, num_decls, head, def);
}

/**
   \brief Detect macros of the form 
   1- (forall (X) (= (+ (f X) (R X)) c))
   2- (forall (X) (<= (+ (f X) (R X)) c))
   3- (forall (X) (>= (+ (f X) (R X)) c))

   The second and third cases are first converted into
   (forall (X) (= (f X) (+ c (* -1 (R x)) (k X))))
   and 
   (forall (X) (<= (k X) 0)) when case 2
   (forall (X) (>= (k X) 0)) when case 3

   For case 2 & 3, the new quantifiers are stored in new_exprs and new_prs.
*/
bool macro_finder::is_arith_macro(expr * n, proof * pr, expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    if (!is_quantifier(n) || !to_quantifier(n)->is_forall())
        return false;
    arith_simplifier_plugin * as = get_arith_simp();
    arith_util & autil = as->get_arith_util();
    expr * body        = to_quantifier(n)->get_expr();
    unsigned num_decls = to_quantifier(n)->get_num_decls();
    
    if (!autil.is_le(body) && !autil.is_ge(body) && !m_manager.is_eq(body))
        return false;
    if (!as->is_add(to_app(body)->get_arg(0)))
        return false;
    app_ref head(m_manager);
    expr_ref def(m_manager);
    bool inv = false;
    if (!m_util.is_arith_macro(body, num_decls, head, def, inv))
        return false;
    app_ref new_body(m_manager);
    
    if (!inv || m_manager.is_eq(body))
        new_body = m_manager.mk_app(to_app(body)->get_decl(), head, def);
    else if (as->is_le(body))
        new_body = autil.mk_ge(head, def);
    else
        new_body = autil.mk_le(head, def);

    quantifier_ref new_q(m_manager); 
    new_q = m_manager.update_quantifier(to_quantifier(n), new_body);
    proof * new_pr      = 0;
    if (m_manager.proofs_enabled()) {
        proof * rw  = m_manager.mk_rewrite(n, new_q);
        new_pr      = m_manager.mk_modus_ponens(pr, rw);
    }
    if (m_manager.is_eq(body)) {
        return m_macro_manager.insert(head->get_decl(), new_q, new_pr);
    }
    // is ge or le
    // 
    TRACE("macro_finder", tout << "is_arith_macro: is_ge or is_le\n";);
    func_decl * f   = head->get_decl();
    func_decl * k   = m_manager.mk_fresh_func_decl(f->get_name(), symbol::null, f->get_arity(), f->get_domain(), f->get_range());
    app * k_app     = m_manager.mk_app(k, head->get_num_args(), head->get_args());
    expr_ref_buffer new_rhs_args(m_manager);
    expr_ref new_rhs2(m_manager);
    as->mk_add(def, k_app, new_rhs2);
    expr * body1    = m_manager.mk_eq(head, new_rhs2);
    expr * body2    = m_manager.mk_app(new_body->get_decl(), k_app, as->mk_numeral(rational(0)));
    quantifier * q1 = m_manager.update_quantifier(new_q, body1);
    expr * patterns[1] = { m_manager.mk_pattern(k_app) };
    quantifier * q2 = m_manager.update_quantifier(new_q, 1, patterns, body2);
    new_exprs.push_back(q1);
    new_exprs.push_back(q2);
    if (m_manager.proofs_enabled()) {
        // new_pr  : new_q
        // rw  : [rewrite] new_q ~ q1 & q2
        // mp  : [modus_pones new_pr rw] q1 & q2
        // pr1 : [and-elim mp] q1
        // pr2 : [and-elim mp] q2
        app * q1q2  = m_manager.mk_and(q1,q2);
        proof * rw  = m_manager.mk_oeq_rewrite(new_q, q1q2);
        proof * mp  = m_manager.mk_modus_ponens(new_pr, rw);
        proof * pr1 = m_manager.mk_and_elim(mp, 0);
        proof * pr2 = m_manager.mk_and_elim(mp, 1);
        new_prs.push_back(pr1);
        new_prs.push_back(pr2);
    }
    return true;
}

/**
   n is of the form: (forall (X) (iff (= (f X) t) def[X]))

   Convert it into:
   
   (forall (X) (= (f X) (ite def[X] t (k X))))
   (forall (X) (not (= (k X) t)))

   where k is a fresh symbol.

   The new quantifiers and proofs are stored in new_exprs and new_prs
*/
static void pseudo_predicate_macro2macro(ast_manager & m, app * head, app * t, expr * def, quantifier * q, proof * pr, 
                                         expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    func_decl * f = head->get_decl();
    func_decl * k = m.mk_fresh_func_decl(f->get_name(), symbol::null, f->get_arity(), f->get_domain(), f->get_range());
    app * k_app   = m.mk_app(k, head->get_num_args(), head->get_args());
    app * ite     = m.mk_ite(def, t, k_app);
    app * body_1  = m.mk_eq(head, ite); 
    app * body_2  = m.mk_not(m.mk_eq(k_app, t));
    quantifier * q1 = m.update_quantifier(q, body_1);
    expr * pats[1] = { m.mk_pattern(k_app) };
    quantifier * q2 = m.update_quantifier(q, 1, pats, body_2); // erase patterns
    new_exprs.push_back(q1);
    new_exprs.push_back(q2);
    if (m.proofs_enabled()) {
        // r  : [rewrite] q ~ q1 & q2
        // pr : q
        // mp : [modus_pones pr pr1] q1 & q2
        // pr1 : [and-elim mp] q1
        // pr2 : [and-elim mp] q2
        app * q1q2  = m.mk_and(q1,q2);
        proof * r   = m.mk_oeq_rewrite(q, q1q2);
        proof * mp  = m.mk_modus_ponens(pr, r);
        proof * pr1 = m.mk_and_elim(mp, 0);
        proof * pr2 = m.mk_and_elim(mp, 1);
        new_prs.push_back(pr1);
        new_prs.push_back(pr2);
    }
}

macro_finder::macro_finder(ast_manager & m, macro_manager & mm):
    m_manager(m),
    m_macro_manager(mm),
    m_util(mm.get_util()) {
}

macro_finder::~macro_finder() {
}

bool macro_finder::expand_macros(unsigned num, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    TRACE("macro_finder", tout << "starting expand_macros:\n";
          m_macro_manager.display(tout););
    bool found_new_macro = false;
    for (unsigned i = 0; i < num; i++) {
        expr * n       = exprs[i];
        proof * pr     = m_manager.proofs_enabled() ? prs[i] : 0;
        expr_ref new_n(m_manager);
        proof_ref new_pr(m_manager);
        m_macro_manager.expand_macros(n, pr, new_n, new_pr);
        app * head = 0;
        expr * def = 0;
        app * t    = 0;
        if (is_macro(new_n, head, def) && m_macro_manager.insert(head->get_decl(), to_quantifier(new_n.get()), new_pr)) {
            TRACE("macro_finder_found", tout << "found new macro: " << head->get_decl()->get_name() << "\n" << mk_pp(new_n, m_manager) << "\n";);
            found_new_macro = true;
        }
        else if (is_arith_macro(new_n, new_pr, new_exprs, new_prs)) {
            TRACE("macro_finder_found", tout << "found new arith macro:\n" << mk_pp(new_n, m_manager) << "\n";);
            found_new_macro = true;
        }
        else if (m_util.is_pseudo_predicate_macro(new_n, head, t, def)) { 
            TRACE("macro_finder_found", tout << "found new pseudo macro:\n" << mk_pp(head, m_manager) << "\n" << mk_pp(t, m_manager) << "\n" << 
                  mk_pp(def, m_manager) << "\n";);
            pseudo_predicate_macro2macro(m_manager, head, t, def, to_quantifier(new_n), new_pr, new_exprs, new_prs);
            found_new_macro = true;
        }
        else {
            new_exprs.push_back(new_n);
            if (m_manager.proofs_enabled())
                new_prs.push_back(new_pr);
        }
    }
    return found_new_macro;
}

void macro_finder::operator()(unsigned num, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs) {
    TRACE("macro_finder", tout << "processing macros...\n";);
    expr_ref_vector   _new_exprs(m_manager);
    proof_ref_vector  _new_prs(m_manager);
    if (expand_macros(num, exprs, prs, _new_exprs, _new_prs)) {
        while (true) {
            expr_ref_vector  old_exprs(m_manager);
            proof_ref_vector old_prs(m_manager);
            _new_exprs.swap(old_exprs);
            _new_prs.swap(old_prs);
            SASSERT(_new_exprs.empty());
            SASSERT(_new_prs.empty());
            if (!expand_macros(old_exprs.size(), old_exprs.c_ptr(), old_prs.c_ptr(), _new_exprs, _new_prs))
                break;
        }
    }
    new_exprs.append(_new_exprs);
    new_prs.append(_new_prs);
}


