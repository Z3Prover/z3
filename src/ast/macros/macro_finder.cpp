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

#include "ast/macros/macro_finder.h"
#include "ast/occurs.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

bool macro_finder::is_macro(expr * n, app_ref & head, expr_ref & def) {
    if (!is_quantifier(n) || !to_quantifier(n)->is_forall())
        return false;
    TRACE("macro_finder", tout << "processing: " << mk_pp(n, m) << "\n";);
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
bool macro_finder::is_arith_macro(expr * n, proof * pr, expr_dependency * dep, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps) {
    if (!is_quantifier(n) || !to_quantifier(n)->is_forall())
        return false;
    expr * body        = to_quantifier(n)->get_expr();
    unsigned num_decls = to_quantifier(n)->get_num_decls();
    
    if (!m_autil.is_le(body) && !m_autil.is_ge(body) && !m.is_eq(body))
        return false;
    if (!m_autil.is_add(to_app(body)->get_arg(0)))
        return false;
    app_ref head(m);
    expr_ref def(m);
    bool inv = false;
    if (!m_util.is_arith_macro(body, num_decls, head, def, inv))
        return false;
    app_ref new_body(m);

    if (!inv || m.is_eq(body))
        new_body = m.mk_app(to_app(body)->get_decl(), head, def);
    else if (m_autil.is_le(body))
        new_body = m_autil.mk_ge(head, def);
    else
        new_body = m_autil.mk_le(head, def);

    quantifier_ref new_q(m);
    new_q = m.update_quantifier(to_quantifier(n), new_body);
    proof * new_pr      = nullptr;
    if (m.proofs_enabled()) {
        proof * rw  = m.mk_rewrite(n, new_q);
        new_pr      = m.mk_modus_ponens(pr, rw);
    }
    expr_dependency * new_dep = dep;
    if (m.is_eq(body)) {
        return m_macro_manager.insert(head->get_decl(), new_q, new_pr, new_dep);
    }
    // is ge or le
    //
    TRACE("macro_finder", tout << "is_arith_macro: is_ge or is_le\n";);
    func_decl * f   = head->get_decl();
    func_decl * k   = m.mk_fresh_func_decl(f->get_name(), symbol::null, f->get_arity(), f->get_domain(), f->get_range());
    app * k_app     = m.mk_app(k, head->get_num_args(), head->get_args());
    expr_ref_buffer new_rhs_args(m);
    expr_ref new_rhs2(m_autil.mk_add(def, k_app), m);
    expr * body1    = m.mk_eq(head, new_rhs2);
    expr * body2    = m.mk_app(new_body->get_decl(), k_app, m_autil.mk_int(0));
    quantifier * q1 = m.update_quantifier(new_q, body1);
    expr * patterns[1] = { m.mk_pattern(k_app) };
    quantifier * q2 = m.update_quantifier(new_q, 1, patterns, body2);
    new_exprs.push_back(q1);
    new_exprs.push_back(q2);
    if (m.proofs_enabled()) {
        // new_pr  : new_q
        // rw  : [rewrite] new_q ~ q1 & q2
        // mp  : [modus_pones new_pr rw] q1 & q2
        // pr1 : [and-elim mp] q1
        // pr2 : [and-elim mp] q2
        app * q1q2  = m.mk_and(q1,q2);
        proof * rw  = m.mk_oeq_rewrite(new_q, q1q2);
        proof * mp  = m.mk_modus_ponens(new_pr, rw);
        proof * pr1 = m.mk_and_elim(mp, 0);
        proof * pr2 = m.mk_and_elim(mp, 1);
        new_prs.push_back(pr1);
        new_prs.push_back(pr2);
    }
    if (dep) {
        new_deps.push_back(new_dep);
        new_deps.push_back(new_dep);
    }
    return true;
}

bool macro_finder::is_arith_macro(expr * n, proof * pr, vector<justified_expr>& new_fmls) {
    if (!is_quantifier(n) || !to_quantifier(n)->is_forall())
        return false;
    expr * body        = to_quantifier(n)->get_expr();
    unsigned num_decls = to_quantifier(n)->get_num_decls();
    
    if (!m_autil.is_le(body) && !m_autil.is_ge(body) && !m.is_eq(body))
        return false;
    if (!m_autil.is_add(to_app(body)->get_arg(0)))
        return false;
    app_ref head(m);
    expr_ref def(m);
    bool inv = false;
    if (!m_util.is_arith_macro(body, num_decls, head, def, inv))
        return false;
    app_ref new_body(m);
    
    if (!inv || m.is_eq(body))
        new_body = m.mk_app(to_app(body)->get_decl(), head, def);
    else if (m_autil.is_le(body))
        new_body = m_autil.mk_ge(head, def);
    else
        new_body = m_autil.mk_le(head, def);

    quantifier_ref new_q(m); 
    new_q = m.update_quantifier(to_quantifier(n), new_body);
    proof * new_pr      = nullptr;
    if (m.proofs_enabled()) {
        proof * rw  = m.mk_rewrite(n, new_q);
        new_pr      = m.mk_modus_ponens(pr, rw);
    }
    if (m.is_eq(body)) {
        return m_macro_manager.insert(head->get_decl(), new_q, new_pr);
    }
    // is ge or le
    // 
    TRACE("macro_finder", tout << "is_arith_macro: is_ge or is_le\n";);
    func_decl * f   = head->get_decl();
    func_decl * k   = m.mk_fresh_func_decl(f->get_name(), symbol::null, f->get_arity(), f->get_domain(), f->get_range());
    app * k_app     = m.mk_app(k, head->get_num_args(), head->get_args());
    expr_ref_buffer new_rhs_args(m);
    expr_ref new_rhs2(m_autil.mk_add(def, k_app), m);
    expr * body1    = m.mk_eq(head, new_rhs2);
    expr * body2    = m.mk_app(new_body->get_decl(), k_app, m_autil.mk_int(0));
    quantifier * q1 = m.update_quantifier(new_q, body1);
    expr * patterns[1] = { m.mk_pattern(k_app) };
    quantifier * q2 = m.update_quantifier(new_q, 1, patterns, body2);
    proof* pr1 = nullptr, *pr2 = nullptr;
    if (m.proofs_enabled()) {
        // new_pr  : new_q
        // rw  : [rewrite] new_q ~ q1 & q2
        // mp  : [modus_pones new_pr rw] q1 & q2
        // pr1 : [and-elim mp] q1
        // pr2 : [and-elim mp] q2
        app * q1q2  = m.mk_and(q1,q2);
        proof * rw  = m.mk_oeq_rewrite(new_q, q1q2);
        proof * mp  = m.mk_modus_ponens(new_pr, rw);
        pr1 = m.mk_and_elim(mp, 0);
        pr2 = m.mk_and_elim(mp, 1);
    }
    new_fmls.push_back(justified_expr(m, q1, pr1));
    new_fmls.push_back(justified_expr(m, q2, pr2));
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
static void pseudo_predicate_macro2macro(ast_manager & m, app * head, app * t, expr * def, quantifier * q, proof * pr, expr_dependency * dep,
                                         expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps ) {
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
    new_deps.push_back(dep);
    new_deps.push_back(dep);
}

static void pseudo_predicate_macro2macro(ast_manager & m, app * head, app * t, expr * def, quantifier * q, proof * pr, 
                                         vector<justified_expr>& new_fmls) {
    func_decl * f = head->get_decl();
    func_decl * k = m.mk_fresh_func_decl(f->get_name(), symbol::null, f->get_arity(), f->get_domain(), f->get_range());
    app * k_app   = m.mk_app(k, head->get_num_args(), head->get_args());
    app * ite     = m.mk_ite(def, t, k_app);
    app * body_1  = m.mk_eq(head, ite); 
    app * body_2  = m.mk_not(m.mk_eq(k_app, t));
    quantifier * q1 = m.update_quantifier(q, body_1);
    proof * pr1 = nullptr, *pr2 = nullptr;
    expr * pats[1] = { m.mk_pattern(k_app) };
    quantifier * q2 = m.update_quantifier(q, 1, pats, body_2); // erase patterns
    if (m.proofs_enabled()) {
        // r  : [rewrite] q ~ q1 & q2
        // pr : q
        // mp : [modus_pones pr pr1] q1 & q2
        // pr1 : [and-elim mp] q1
        // pr2 : [and-elim mp] q2
        app * q1q2  = m.mk_and(q1,q2);
        proof * r   = m.mk_oeq_rewrite(q, q1q2);
        proof * mp  = m.mk_modus_ponens(pr, r);
        pr1 = m.mk_and_elim(mp, 0);
        pr2 = m.mk_and_elim(mp, 1);
    }
    new_fmls.push_back(justified_expr(m, q1, pr1));
    new_fmls.push_back(justified_expr(m, q2, pr2));
}

macro_finder::macro_finder(ast_manager & m, macro_manager & mm):
    m(m),
    m_macro_manager(mm),
    m_util(mm.get_util()),
    m_autil(m) {
}

macro_finder::~macro_finder() {
}

bool macro_finder::expand_macros(unsigned num, expr * const * exprs, proof * const * prs, expr_dependency * const * deps,  expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps) {
    TRACE("macro_finder", tout << "starting expand_macros:\n";
          m_macro_manager.display(tout););
    bool found_new_macro = false;
    for (unsigned i = 0; i < num; i++) {
        expr * n       = exprs[i];
        proof * pr     = m.proofs_enabled() ? prs[i] : nullptr;
        expr_dependency * depi = deps != nullptr ? deps[i] : nullptr;
        expr_ref new_n(m), def(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        m_macro_manager.expand_macros(n, pr, depi, new_n, new_pr, new_dep);
        app_ref head(m), t(m);
        if (is_macro(new_n, head, def) && m_macro_manager.insert(head->get_decl(), to_quantifier(new_n.get()), new_pr, new_dep)) {
            TRACE("macro_finder_found", tout << "found new macro: " << head->get_decl()->get_name() << "\n" << new_n << "\n";);
            found_new_macro = true;
        }
        else if (is_arith_macro(new_n, new_pr, new_dep, new_exprs, new_prs, new_deps)) {
            TRACE("macro_finder_found", tout << "found new arith macro:\n" << new_n << "\n";);
            found_new_macro = true;
        }
        else if (m_util.is_pseudo_predicate_macro(new_n, head, t, def)) {
            TRACE("macro_finder_found", tout << "found new pseudo macro:\n" << head << "\n" << t << "\n" << def << "\n";);
            pseudo_predicate_macro2macro(m, head, t, def, to_quantifier(new_n), new_pr, new_dep, new_exprs, new_prs, new_deps);
            found_new_macro = true;
        }
        else {
            new_exprs.push_back(new_n);
            if (m.proofs_enabled())
                new_prs.push_back(new_pr);
            if (deps != nullptr)
                new_deps.push_back(new_dep);
        }
    }
    return found_new_macro;
}

void macro_finder::operator()(unsigned num, expr * const * exprs, proof * const * prs, expr_dependency * const * deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps) {
    TRACE("macro_finder", tout << "processing macros...\n";);
    expr_ref_vector   _new_exprs(m);
    proof_ref_vector  _new_prs(m);
    expr_dependency_ref_vector _new_deps(m);
    if (expand_macros(num, exprs, prs, deps, _new_exprs, _new_prs, _new_deps)) {
        while (true) {
            expr_ref_vector  old_exprs(m);
            proof_ref_vector old_prs(m);
            expr_dependency_ref_vector old_deps(m);
            _new_exprs.swap(old_exprs);
            _new_prs.swap(old_prs);
            _new_deps.swap(old_deps);
            SASSERT(_new_exprs.empty());
            SASSERT(_new_prs.empty());
            SASSERT(_new_deps.empty());
            if (!expand_macros(old_exprs.size(), old_exprs.c_ptr(), old_prs.c_ptr(), old_deps.c_ptr(),
                               _new_exprs, _new_prs, _new_deps))
                break;
        }
    }
    new_exprs.append(_new_exprs);
    new_prs.append(_new_prs);
    new_deps.append(_new_deps);
}



bool macro_finder::expand_macros(unsigned num, justified_expr const * fmls, vector<justified_expr>& new_fmls) {
    TRACE("macro_finder", tout << "starting expand_macros:\n";
          m_macro_manager.display(tout););
    bool found_new_macro = false;
    for (unsigned i = 0; i < num; i++) {
        expr * n       = fmls[i].get_fml();
        proof * pr     = m.proofs_enabled() ? fmls[i].get_proof() : nullptr;
        expr_ref new_n(m), def(m);
        proof_ref new_pr(m);
        expr_dependency_ref new_dep(m);
        m_macro_manager.expand_macros(n, pr, nullptr, new_n, new_pr, new_dep);
        app_ref head(m), t(m);
        if (is_macro(new_n, head, def) && m_macro_manager.insert(head->get_decl(), to_quantifier(new_n.get()), new_pr)) {
            TRACE("macro_finder_found", tout << "found new macro: " << head->get_decl()->get_name() << "\n" << new_n << "\n";);
            found_new_macro = true;
        }
        else if (is_arith_macro(new_n, new_pr, new_fmls)) {
            TRACE("macro_finder_found", tout << "found new arith macro:\n" << new_n << "\n";);
            found_new_macro = true;
        }
        else if (m_util.is_pseudo_predicate_macro(new_n, head, t, def)) { 
            TRACE("macro_finder_found", tout << "found new pseudo macro:\n" << head << "\n" << t << "\n" << def << "\n";);
            pseudo_predicate_macro2macro(m, head, t, def, to_quantifier(new_n), new_pr, new_fmls);
            found_new_macro = true;
        }
        else {
            new_fmls.push_back(justified_expr(m, new_n, new_pr));
        }
    }
    return found_new_macro;
}

void macro_finder::operator()(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls) {
    TRACE("macro_finder", tout << "processing macros...\n";);
    vector<justified_expr> _new_fmls;
    if (expand_macros(n, fmls, _new_fmls)) {
        while (true) {
            vector<justified_expr> old_fmls;
            _new_fmls.swap(old_fmls);
            SASSERT(_new_fmls.empty());
            if (!expand_macros(old_fmls.size(), old_fmls.c_ptr(), _new_fmls))
                break;
        }
    }
    new_fmls.append(_new_fmls);
}


