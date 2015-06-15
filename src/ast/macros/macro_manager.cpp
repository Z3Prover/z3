/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    macro_manager.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-05.

Revision History:

    Christoph Wintersteiger (t-cwinte), 2010-04-13: Added cycle detection for macro definitions
    Leonardo de Moura (leonardo) 2010-12-15: Moved dependency management to func_decl_dependencies.h

--*/
#include"macro_manager.h"
#include"for_each_expr.h"
#include"var_subst.h"
#include"ast_pp.h"
#include"recurse_expr_def.h"

macro_manager::macro_manager(ast_manager & m, simplifier & s):
    m_manager(m),
    m_simplifier(s),
    m_util(m, s),
    m_decls(m),
    m_macros(m),
    m_macro_prs(m),
    m_forbidden(m),
    m_deps(m) {
    m_util.set_forbidden_set(&m_forbidden_set);
}

macro_manager::~macro_manager() {
}

void macro_manager::push_scope() {
    m_scopes.push_back(scope());
    scope & s              = m_scopes.back();
    s.m_decls_lim          = m_decls.size();
    s.m_forbidden_lim      = m_forbidden.size();
}

void macro_manager::pop_scope(unsigned num_scopes) {
    unsigned new_lvl    = m_scopes.size() - num_scopes;
    scope & s           = m_scopes[new_lvl];
    restore_decls(s.m_decls_lim);
    restore_forbidden(s.m_forbidden_lim);
    m_scopes.shrink(new_lvl);
}

void macro_manager::restore_decls(unsigned old_sz) {
    unsigned sz         = m_decls.size();
    for (unsigned i = old_sz; i < sz; i++) {
        m_decl2macro.erase(m_decls.get(i));
        m_deps.erase(m_decls.get(i));
        if (m_manager.proofs_enabled())
            m_decl2macro_pr.erase(m_decls.get(i));
    }
    m_decls.shrink(old_sz);
    m_macros.shrink(old_sz);
    if (m_manager.proofs_enabled())
        m_macro_prs.shrink(old_sz);
}

void macro_manager::restore_forbidden(unsigned old_sz) {
    unsigned sz         = m_forbidden.size();
    for (unsigned i = old_sz; i < sz; i++)
        m_forbidden_set.erase(m_forbidden.get(i));
    m_forbidden.shrink(old_sz);
}

void macro_manager::reset() {
    m_decl2macro.reset();
    m_decl2macro_pr.reset();
    m_decls.reset();
    m_macros.reset();
    m_macro_prs.reset();
    m_scopes.reset();
    m_forbidden_set.reset();
    m_forbidden.reset();
    m_deps.reset();
}

bool macro_manager::insert(func_decl * f, quantifier * m, proof * pr) {
    TRACE("macro_insert", tout << "trying to create macro: " << f->get_name() << "\n" << mk_pp(m, m_manager) << "\n";);

    // if we already have a macro for f then return false;
    if (m_decls.contains(f)) {
        TRACE("macro_insert", tout << "we already have a macro for: " << f->get_name() << "\n";);
        return false;
    }

    app * head;
    expr * definition;
    get_head_def(m, f, head, definition);

    func_decl_set * s = m_deps.mk_func_decl_set();
    m_deps.collect_func_decls(definition, s);
    if (!m_deps.insert(f, s)) {
        return false;
    }
    
    // add macro
    m_decl2macro.insert(f, m);
    m_decls.push_back(f);
    m_macros.push_back(m);
    if (m_manager.proofs_enabled()) {
        m_macro_prs.push_back(pr);
        m_decl2macro_pr.insert(f, pr);
    }

    TRACE("macro_insert", tout << "A macro was successfully created for: " << f->get_name() << "\n";);
    
    // Nothing's forbidden anymore; if something's bad, we detected it earlier. 
    // mark_forbidden(m->get_expr());
    return true;
}

namespace macro_manager_ns {
    struct proc {
        obj_hashtable<func_decl> &  m_forbidden_set;
        func_decl_ref_vector     &  m_forbidden;
        proc(obj_hashtable<func_decl> & s, func_decl_ref_vector & v):m_forbidden_set(s), m_forbidden(v) {}
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app * n) {
            func_decl * d = n->get_decl();
            if (n->get_num_args() > 0 && n->get_family_id() == null_family_id && !m_forbidden_set.contains(d)) {
                m_forbidden_set.insert(d);
                m_forbidden.push_back(d);
            }
        }
    };
};

/**
   \brief Mark all func_decls used in exprs as forbidden.
*/
void macro_manager::mark_forbidden(unsigned n, expr * const * exprs) {
    expr_mark visited; 
    macro_manager_ns::proc p(m_forbidden_set, m_forbidden);
    for (unsigned i = 0; i < n; i++)
        for_each_expr(p, visited, exprs[i]);
}

void macro_manager::get_head_def(quantifier * q, func_decl * d, app * & head, expr * & def) const {
    app * body = to_app(q->get_expr());
    SASSERT(m_manager.is_eq(body) || m_manager.is_iff(body));
    expr * lhs = to_app(body)->get_arg(0);
    expr * rhs = to_app(body)->get_arg(1);
    SASSERT(is_app_of(lhs, d) || is_app_of(rhs, d));
    SASSERT(!is_app_of(lhs, d) || !is_app_of(rhs, d));
    if (is_app_of(lhs, d)) {
        head = to_app(lhs);
        def  = rhs;
    }
    else {
        head = to_app(rhs);
        def  = lhs;
    }
}

void macro_manager::display(std::ostream & out) {
    unsigned sz = m_decls.size();
    for (unsigned i = 0; i < sz; i++) {
        func_decl * f  = m_decls.get(i);
        quantifier * q = 0;
        m_decl2macro.find(f, q);
        app * head;
        expr * def;
        get_head_def(q, f, head, def);
        SASSERT(q);
        out << mk_pp(head, m_manager) << " ->\n" << mk_pp(def, m_manager) << "\n";
    }
}

func_decl * macro_manager::get_macro_interpretation(unsigned i, expr_ref & interp) const {
    func_decl * f  = m_decls.get(i);
    quantifier * q = m_macros.get(i);
    app * head;
    expr * def;
    get_head_def(q, f, head, def);
    TRACE("macro_bug", 
          tout << f->get_name() << "\n" << mk_pp(head, m_manager) << "\n" << mk_pp(q, m_manager) << "\n";);
    m_util.mk_macro_interpretation(head, def, interp);
    return f;
}

macro_manager::macro_expander::macro_expander(ast_manager & m, macro_manager & mm, simplifier & s):
    simplifier(m),
    m_macro_manager(mm) {
    // REMARK: theory simplifier should not be used by macro_expander...
    // is_arith_macro rewrites a quantifer such as:
    //   forall (x Int) (= (+ x (+ (f x) 1)) 2)
    // into
    //   forall (x Int) (= (f x) (+ 1 (* -1 x)))
    // The goal is to make simple macro detection detect the arith macro.
    // The arith simplifier will undo this transformation.
    // borrow_plugins(s);
    enable_ac_support(false);
}

macro_manager::macro_expander::~macro_expander() {
    // release_plugins();
}

void macro_manager::macro_expander::reduce1_quantifier(quantifier * q) {
    simplifier::reduce1_quantifier(q);
    // If a macro was expanded in a pattern, we must erase it since it may not be a valid pattern anymore.
    // The MAM assumes valid patterns, and it crashes if invalid patterns are provided.
    // For example, it will crash if the pattern does not contain all variables.
    //
    // Alternative solution: use pattern_validation to check if the pattern is still valid.
    // I'm not sure if this is a good solution, since the pattern may be meaningless after the macro expansion.
    // So, I'm just erasing them.
    expr *  new_q_expr = 0;
    proof * new_q_pr = 0;
    get_cached(q, new_q_expr, new_q_pr);
    if (!is_quantifier(new_q_expr))
        return;
    quantifier * new_q = to_quantifier(new_q_expr);
    bool erase_patterns = false;
    if (q->get_num_patterns() != new_q->get_num_patterns() ||
        q->get_num_no_patterns() != new_q->get_num_no_patterns()) {
        erase_patterns = true;
    }
    else {
        for (unsigned i = 0; !erase_patterns && i < q->get_num_patterns(); i++) {
            if (q->get_pattern(i) != new_q->get_pattern(i))
                erase_patterns = true;
        }
        for (unsigned i = 0; !erase_patterns && i < q->get_num_no_patterns(); i++) {
            if (q->get_no_pattern(i) != new_q->get_no_pattern(i)) 
                erase_patterns = true;
        }
    }
    if (erase_patterns) {
        ast_manager & m = get_manager();
        expr * new_new_q = m.update_quantifier(new_q, 0, 0, 0, 0, new_q->get_expr());
        // we can use the same proof since new_new_q and new_q are identical modulo patterns/annotations
        cache_result(q, new_new_q, new_q_pr);
    }
}

bool macro_manager::macro_expander::get_subst(expr * _n, expr_ref & r, proof_ref & p) {
    if (!is_app(_n))
        return false;
    app * n = to_app(_n);
    quantifier * q = 0;
    func_decl * d  = n->get_decl(); 
    TRACE("macro_manager_bug", tout << "trying to expand:\n" << mk_pp(n, m) << "\nd:\n" << d->get_name() << "\n";);
    if (m_macro_manager.m_decl2macro.find(d, q)) {
        TRACE("macro_manager", tout << "expanding: " << mk_pp(n, m) << "\n";);
        app * head = 0;
        expr * def = 0;
        m_macro_manager.get_head_def(q, d, head, def);
        unsigned num = n->get_num_args();
        SASSERT(head && def);
        ptr_buffer<expr> subst_args;
        subst_args.resize(num, 0);
        for (unsigned i = 0; i < num; i++) {
            var * v = to_var(head->get_arg(i));
            SASSERT(v->get_idx() < num);
            unsigned nidx = num - v->get_idx() - 1;
            SASSERT(subst_args[nidx] == 0);
            subst_args[nidx] = n->get_arg(i);
        }
        var_subst s(m);
        s(def, num, subst_args.c_ptr(), r);
        if (m.proofs_enabled()) {
            expr_ref instance(m);
            s(q->get_expr(), num, subst_args.c_ptr(), instance);
            proof * qi_pr = m.mk_quant_inst(m.mk_or(m.mk_not(q), instance), num, subst_args.c_ptr());
            proof * q_pr  = 0;
            m_macro_manager.m_decl2macro_pr.find(d, q_pr);
            SASSERT(q_pr != 0);
            proof * prs[2] = { qi_pr, q_pr };
            p = m.mk_unit_resolution(2, prs);
        }
        else {
            p = 0;
        }
        return true;
    }
    return false;
}

void macro_manager::expand_macros(expr * n, proof * pr, expr_ref & r, proof_ref & new_pr) {
    if (has_macros()) {
        // Expand macros with "real" proof production support (NO rewrite*)
        expr_ref old_n(m_manager);
        proof_ref old_pr(m_manager);
        old_n  = n;
        old_pr = pr;
        for (;;) {
            macro_expander proc(m_manager, *this, m_simplifier);
            proof_ref n_eq_r_pr(m_manager);
            TRACE("macro_manager_bug", tout << "expand_macros:\n" << mk_pp(n, m_manager) << "\n";);
            proc(old_n, r, n_eq_r_pr);
            new_pr = m_manager.mk_modus_ponens(old_pr, n_eq_r_pr);
            if (r.get() == old_n.get())
                return;
            old_n  = r;
            old_pr = new_pr; 
        }
    }
    else {
        r      = n;
        new_pr = pr;
    }
}

