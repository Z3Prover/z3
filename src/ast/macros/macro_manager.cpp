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
#include "ast/macros/macro_manager.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_pp.h"
#include "ast/recurse_expr_def.h"


macro_manager::macro_manager(ast_manager & m):
    m(m),
    m_util(m),
    m_decls(m),
    m_macros(m),
    m_macro_prs(m),
    m_macro_deps(m),
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
        if (m.proofs_enabled())
            m_decl2macro_pr.erase(m_decls.get(i));
        m_decl2macro_dep.erase(m_decls.get(i));
    }
    m_decls.shrink(old_sz);
    m_macros.shrink(old_sz);
    if (m.proofs_enabled())
        m_macro_prs.shrink(old_sz);
    m_macro_deps.shrink(old_sz);
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
    m_decl2macro_dep.reset();
    m_decls.reset();
    m_macros.reset();
    m_macro_prs.reset();
    m_macro_deps.reset();
    m_scopes.reset();
    m_forbidden_set.reset();
    m_forbidden.reset();
    m_deps.reset();
}

bool macro_manager::insert(func_decl * f, quantifier * q, proof * pr, expr_dependency* dep) {
    TRACE("macro_insert", tout << "trying to create macro: " << f->get_name() << "\n" << mk_pp(q, m) << "\n";);

    // if we already have a macro for f then return false;
    if (m_decls.contains(f)) {
        TRACE("macro_insert", tout << "we already have a macro for: " << f->get_name() << "\n";);
        return false;
    }

    app * head;
    expr * definition;
    get_head_def(q, f, head, definition);

    func_decl_set * s = m_deps.mk_func_decl_set();
    m_deps.collect_func_decls(definition, s);
    if (!m_deps.insert(f, s)) {
        return false;
    }

    // add macro
    m_decl2macro.insert(f, q);
    m_decls.push_back(f);
    m_macros.push_back(q);
    if (m.proofs_enabled()) {
        m_macro_prs.push_back(pr);
        m_decl2macro_pr.insert(f, pr);
    }
    m_macro_deps.push_back(dep);
    m_decl2macro_dep.insert(f, dep);

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

void macro_manager::mark_forbidden(unsigned n, justified_expr const * exprs) {
    expr_mark visited;
    macro_manager_ns::proc p(m_forbidden_set, m_forbidden);
    for (unsigned i = 0; i < n; i++)
        for_each_expr(p, visited, exprs[i].get_fml());
}


void macro_manager::get_head_def(quantifier * q, func_decl * d, app * & head, expr * & def) const {
    app * body = to_app(q->get_expr());
    SASSERT(m.is_eq(body) || m.is_iff(body));
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
        quantifier * q = nullptr;
        m_decl2macro.find(f, q);
        app * head;
        expr * def;
        get_head_def(q, f, head, def);
        SASSERT(q);
        out << mk_pp(head, m) << " ->\n" << mk_pp(def, m) << "\n";
    }
}

func_decl * macro_manager::get_macro_interpretation(unsigned i, expr_ref & interp) const {
    func_decl * f  = m_decls.get(i);
    quantifier * q = m_macros.get(i);
    app * head;
    expr * def;
    get_head_def(q, f, head, def);
    TRACE("macro_bug",
          tout << f->get_name() << "\n" << mk_pp(head, m) << "\n" << mk_pp(q, m) << "\n";);
    m_util.mk_macro_interpretation(head, q->get_num_decls(), def, interp);
    return f;
}

struct macro_manager::macro_expander_cfg : public default_rewriter_cfg {
    ast_manager& m; 
    macro_manager& mm;
    expr_dependency_ref m_used_macro_dependencies; 
    expr_ref_vector m_trail;

    macro_expander_cfg(ast_manager& m, macro_manager& mm):
        m(m),
        mm(mm),
        m_used_macro_dependencies(m),
        m_trail(m)
    {}

    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        return BR_FAILED;
    }

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {

        // If a macro was expanded in a pattern, we must erase it since it may not be a valid pattern anymore.
        // The MAM assumes valid patterns, and it crashes if invalid patterns are provided.
        // For example, it will crash if the pattern does not contain all variables.
        //
        // Alternative solution: use pattern_validation to check if the pattern is still valid.
        // I'm not sure if this is a good solution, since the pattern may be meaningless after the macro expansion.
        // So, I'm just erasing them.

        bool erase_patterns = false;
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_patterns(); i++) {
            if (old_q->get_pattern(i) != new_patterns[i]) 
                erase_patterns = true;
        }
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_no_patterns(); i++) {
            if (old_q->get_no_pattern(i) != new_no_patterns[i])
                erase_patterns = true;
        }
        if (erase_patterns) {
            result = m.update_quantifier(old_q, 0, nullptr, 0, nullptr, new_body);
        }
        return erase_patterns;
    }

    bool get_subst(expr * _n, expr* & r, proof* & p) {
        if (!is_app(_n))
            return false;
        app * n = to_app(_n);
        quantifier * q = nullptr;
        func_decl * d  = n->get_decl();
        TRACE("macro_manager", tout << "trying to expand:\n" << mk_pp(n, m) << "\nd:\n" << d->get_name() << "\n";);
        if (mm.m_decl2macro.find(d, q)) {
            TRACE("macro_manager", tout << "expanding: " << mk_pp(n, m) << "\n";);
            app * head = nullptr;
            expr * def = nullptr;
            mm.get_head_def(q, d, head, def);
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
            expr_ref rr(m);
            s(def, num, subst_args.c_ptr(), rr);
            m_trail.push_back(rr);
            r = rr;
            if (m.proofs_enabled()) {
                expr_ref instance(m);
                s(q->get_expr(), num, subst_args.c_ptr(), instance);
                proof * qi_pr = m.mk_quant_inst(m.mk_or(m.mk_not(q), instance), num, subst_args.c_ptr());
                proof * q_pr  = nullptr;
                mm.m_decl2macro_pr.find(d, q_pr);
                SASSERT(q_pr != 0);
                proof * prs[2] = { qi_pr, q_pr };
                p = m.mk_unit_resolution(2, prs);
            }
            else {
                p = nullptr;
            }
            expr_dependency * ed = mm.m_decl2macro_dep.find(d); 
            m_used_macro_dependencies = m.mk_join(m_used_macro_dependencies, ed); 
            return true;
        }
        return false;
    }
};

struct macro_manager::macro_expander_rw : public rewriter_tpl<macro_manager::macro_expander_cfg> {
    macro_expander_cfg m_cfg;

    macro_expander_rw(ast_manager& m, macro_manager& mm):
        rewriter_tpl<macro_manager::macro_expander_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, mm) 
    {}
};


void macro_manager::expand_macros(expr * n, proof * pr, expr_dependency * dep, expr_ref & r, proof_ref & new_pr, expr_dependency_ref & new_dep) {
    if (has_macros()) {
        // Expand macros with "real" proof production support (NO rewrite*)
        expr_ref old_n(m);
        proof_ref old_pr(m);
        expr_dependency_ref old_dep(m);
        old_n  = n;
        old_pr = pr;
        old_dep = dep;
        bool change = false;
        for (;;) {
            macro_expander_rw proc(m, *this);
            proof_ref n_eq_r_pr(m);
            TRACE("macro_manager_bug", tout << "expand_macros:\n" << mk_pp(n, m) << "\n";);
            proc(old_n, r, n_eq_r_pr);
            new_pr = m.mk_modus_ponens(old_pr, n_eq_r_pr);
            new_dep = m.mk_join(old_dep, proc.m_cfg.m_used_macro_dependencies); 
            if (r.get() == old_n.get())
                break;
            old_n  = r;
            old_pr = new_pr;
            old_dep = new_dep;
            change = true;
        }
        // apply th_rewrite to the result.
        if (change) {
            th_rewriter rw(m);
            proof_ref rw_pr(m);
            expr_ref r1(r, m);
            rw(r1, r, rw_pr);
            new_pr = m.mk_modus_ponens(new_pr, rw_pr);
        }
    }
    else {
        r      = n;
        new_pr = pr;
        new_dep = dep;
    }
}

