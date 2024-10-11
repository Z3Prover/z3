/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dominator_simplifier.cpp

Abstract:

    Dominator-based context simplifer.

Author:

    Nikolaj and Nuno 

--*/

#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/simplifiers/dominator_simplifier.h"

dominator_simplifier::~dominator_simplifier() {
    dealloc(m_simplifier);
}

expr_ref dominator_simplifier::simplify_ite(app * ite) {
    expr_ref r(m);
    expr * c = nullptr, *t = nullptr, *e = nullptr;
    VERIFY(m.is_ite(ite, c, t, e));
    unsigned old_lvl = scope_level();
    expr_ref new_c = simplify_arg(c);
    if (m.is_true(new_c)) {
        r = simplify_arg(t);
    } 
    else if (!assert_expr(new_c, false)) {
        r = simplify_arg(e);
    }
    else {
        for (expr * child : tree(ite)) 
            if (is_subexpr(child, t) && !is_subexpr(child, e)) 
                simplify_rec(child);            
        
        local_pop(scope_level() - old_lvl);
        expr_ref new_t = simplify_arg(t);
        reset_cache();
        if (!assert_expr(new_c, true)) {
            return new_t;
        }
        for (expr * child : tree(ite)) 
            if (is_subexpr(child, e) && !is_subexpr(child, t)) 
                simplify_rec(child);
        local_pop(scope_level() - old_lvl);
        expr_ref new_e = simplify_arg(e);

        if (c == new_c && t == new_t && e == new_e) {
            r = ite;
        }
        else if (new_t == new_e) {
            r = new_t;
        }
        else {
            TRACE("simplify", tout << new_c << "\n" << new_t << "\n" << new_e << "\n";);
            r = m.mk_ite(new_c, new_t, new_e);
        }        
    }
    reset_cache();
    return r;
}


expr_ref dominator_simplifier::simplify_arg(expr * e) {
    expr_ref r(m);    
    r = get_cached(e);
    (*m_simplifier)(r);
    CTRACE("simplify", e != r, tout << "depth: " << m_depth << " " << mk_pp(e, m) << " -> " << r << "\n";);
    return r;
}

/**
   \brief simplify e recursively.
*/
expr_ref dominator_simplifier::simplify_rec(expr * e0) {
    expr_ref r(m);
    expr* e = nullptr;

    if (!m_result.find(e0, e)) {
        e = e0;
    }
    
    ++m_depth;
    if (m_depth > m_max_depth) {
        r = e;
    }
    else if (m.is_ite(e)) {
        r = simplify_ite(to_app(e));
    }
    else if (m.is_and(e)) {
        r = simplify_and(to_app(e));
    }
    else if (m.is_or(e)) {
        r = simplify_or(to_app(e));
    }
    else if (m.is_not(e)) {
        r = simplify_not(to_app(e));
    }
    else {
        for (expr * child : tree(e)) {
            if (child != e)
               simplify_rec(child);
        }
        if (is_app(e)) {
            m_args.reset();
            for (expr* arg : *to_app(e)) {
                // we don't have a way to distinguish between e.g.
                // ite(c, f(c), foo)  (which should go to ite(c, f(true), foo))
                // from and(or(x, y), f(x)), where we do a "trial" with x=false
                // Trials are good for boolean formula simplification but not sound
                // for fn applications.
                m_args.push_back(m.is_bool(arg) ? arg : simplify_arg(arg));
            }
            r = m.mk_app(to_app(e)->get_decl(), m_args.size(), m_args.data());
        }
        else {
            r = e;
        }
    }
    CTRACE("simplify", e0 != r, tout << "depth before: " << m_depth << " " << mk_pp(e0, m) << " -> " << r << "\n";);
    (*m_simplifier)(r);
    cache(e0, r);
    CTRACE("simplify", e0 != r, tout << "depth: " << m_depth << " " << mk_pp(e0, m) << " -> " << r << "\n";);
    --m_depth;
    m_subexpr_cache.reset();
    return r;
}

expr_ref dominator_simplifier::simplify_and_or(bool is_and, app * e) {
    expr_ref r(m);
    unsigned old_lvl = scope_level();

    auto is_subexpr_arg = [&](expr * child, expr * except) {
        if (!is_subexpr(child, except))
            return false;
        for (expr * arg : *e) {
            if (arg != except && is_subexpr(child, arg))
                return false;
        }
        return true;
    };

    expr_ref_vector args(m);

    auto simp_arg = [&](expr* arg) {
        for (expr * child : tree(arg)) {                    
            if (is_subexpr_arg(child, arg)) {               
                simplify_rec(child);                        
            }                                               
        }                                                   
        r = simplify_arg(arg);                              
        args.push_back(r);                                  
        if (!assert_expr(r, !is_and)) {                     
            local_pop(scope_level() - old_lvl);                   
            r = is_and ? m.mk_false() : m.mk_true();        
            reset_cache();
            return true;
        }                     
        return false;
    };

    if (m_forward) {
        for (expr * arg : *e) {
            if (simp_arg(arg)) 
                return r;
        }                                                                  
    }
    else {        
        for (unsigned i = e->get_num_args(); i-- > 0; ) {
            if (simp_arg(e->get_arg(i)))
                return r;
        }
        args.reverse();
    }
    
    local_pop(scope_level() - old_lvl);
    reset_cache();
    return { is_and ? mk_and(args) : mk_or(args), m };
}

expr_ref dominator_simplifier::simplify_not(app * e) {
    expr *ee = nullptr;
    VERIFY(m.is_not(e, ee));
    unsigned old_lvl = scope_level();
    expr_ref t = simplify_rec(ee);
    local_pop(scope_level() - old_lvl);
    reset_cache();
    return mk_not(t);
}



bool dominator_simplifier::init() {
    expr_ref_vector args(m);
    for (auto i : indices()) 
        if (!m_fmls[i].dep())
            args.push_back(m_fmls[i].fml());
    expr_ref fml = mk_and(args);
    m_result.reset();
    m_trail.reset();
    return m_dominators.compile(fml);
}


void dominator_simplifier::reduce() {

    m_trail.reset();
    m_args.reset();
    m_result.reset();
    m_dominators.reset();

    SASSERT(scope_level() == 0);
    bool change = true;
    unsigned n  = 0;
    m_depth = 0;
    while (change && n < 10) {
        change = false;
        ++n;

        // go forwards
        m_forward = true;
        if (!init()) return;
        for (unsigned i = qhead(); i < qtail() && !m_fmls.inconsistent(); ++i) {
            auto [f, p, d] = m_fmls[i]();
            if (d)
                continue;

            expr_ref r = simplify_rec(f);
            if (!m.is_true(r) && !m.is_false(r) && !p && !assert_expr(r, false)) 
                r = m.mk_false();
            
            CTRACE("simplify", r != f, tout << r << " " << mk_pp(f, m) << "\n";);
            change |= r != f;
            proof_ref new_pr(m);
            if (p) {
                new_pr = m.mk_modus_ponens(p, m.mk_rewrite(f, r));
            }
            m_fmls.update(i, dependent_expr(m, r, new_pr, d));
        }
        local_pop(scope_level());

        // go backwards
        m_forward = false;
        if (!init()) return;
        for (unsigned i = qtail(); i-- > qhead() && !m_fmls.inconsistent(); ) {

            auto [f, p, d] = m_fmls[i]();
            if (d)
                continue;
            expr_ref r = simplify_rec(f);
            if (!m.is_true(r) && !m.is_false(r) && !p && !assert_expr(r, false)) 
                r = m.mk_false();
            
            change |= r != f;
            CTRACE("simplify", r != f, tout << r << " " << mk_pp(f, m) << "\n";);
            proof_ref new_pr(m);
            if (r) {
                new_pr = m.mk_rewrite(f, r);
                new_pr = m.mk_modus_ponens(p, new_pr);
            }
            m_fmls.update(i, dependent_expr(m, r, new_pr, d));
        }
        local_pop(scope_level());
    }
    SASSERT(scope_level() == 0);
}

/**
   \brief determine if a is dominated by b. 
   Walk the immediate dominators of a upwards until hitting b or a term that is deeper than b.
   Save intermediary results in a cache to avoid recomputations.
*/

bool dominator_simplifier::is_subexpr(expr * a, expr * b) {
    if (a == b)
        return true;

    bool r;
    if (m_subexpr_cache.find(a, b, r))
        return r;

    if (get_depth(a) >= get_depth(b)) {
        return false;
    }
    SASSERT(a != idom(a) && get_depth(idom(a)) > get_depth(a));
    r = is_subexpr(idom(a), b);
    m_subexpr_cache.insert(a, b, r);   
    return r;
}

ptr_vector<expr> const & dominator_simplifier::tree(expr * e) {
    if (auto p = m_dominators.get_tree().find_core(e))
        return p->get_data().get_value();
    return m_empty;
}
