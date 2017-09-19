/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dom_simplify_tactic.cpp

Abstract:

    Dominator-based context simplifer.

Author:

    Nikolaj and Nuno 

Notes:

--*/


#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "tactic/core/dom_simplify_tactic.h"


/**
   \brief compute a post-order traversal for e.
   Also populate the set of parents
*/
void expr_dominators::compute_post_order() {
    unsigned post_num = 0;
    SASSERT(m_post2expr.empty());
    SASSERT(m_expr2post.empty());
    ast_mark mark;
    ptr_vector<expr> todo;
    todo.push_back(m_root);
    while (!todo.empty()) {
        expr* e = todo.back();
        if (mark.is_marked(e)) {
            todo.pop_back();
            continue;
        }
        if (is_app(e)) {
            app* a = to_app(e);
            bool done = true;
            for (expr* arg : *a) {
                if (!mark.is_marked(arg)) {
                    todo.push_back(arg);
                    done = false;
                }
            }
            if (done) {
                mark.mark(e, true);
                m_expr2post.insert(e, post_num++);
                m_post2expr.push_back(e);
                todo.pop_back();
                for (expr* arg : *a) {
                    add_edge(m_parents, arg, a);
                }
            }
        }
        else {
            mark.mark(e, true);
            todo.pop_back();
        }
    }
}

expr* expr_dominators::intersect(expr* x, expr * y) {
    unsigned n1 = m_expr2post[x];
    unsigned n2 = m_expr2post[y];
    while (n1 != n2) {
        if (n1 < n2) {
            x = m_doms[x];
            n1 = m_expr2post[x];
        }
        else if (n1 > n2) {
            y = m_doms[y];
            n2 = m_expr2post[y];
        }
    }
    SASSERT(x == y);
    return x;
}

void expr_dominators::compute_dominators() {
    expr * e = m_root;
    SASSERT(m_doms.empty());
    m_doms.insert(e, e);
    bool change = true;
    while (change) {
        change = false;
        SASSERT(m_post2expr.back() == e);
        for (unsigned i = 0; i < m_post2expr.size() - 1; ++i) {
            expr * child = m_post2expr[i];
            ptr_vector<expr> const& p = m_parents[child];
            SASSERT(!p.empty());
            expr * new_idom = p[0], * idom2 = 0;
            for (unsigned j = 1; j < p.size(); ++j) {
                if (m_doms.find(p[j], idom2)) {
                    new_idom = intersect(new_idom, idom2);
                }
            }
            if (!m_doms.find(child, idom2) || idom2 != new_idom) {
                m_doms.insert(child, new_idom);
                change = true;
            }
        }
    }
}

void expr_dominators::extract_tree() {
    for (auto const& kv : m_doms) {
        add_edge(m_tree, kv.m_value, kv.m_key);
    }
}    

void expr_dominators::compile(expr * e) {
    reset();
    m_root = e;
    compute_post_order();
    compute_dominators();
    extract_tree();
}

void expr_dominators::compile(unsigned sz, expr * const* es) {
    expr_ref e(m.mk_and(sz, es), m);
    compile(e);
}

void expr_dominators::reset() {
    m_expr2post.reset();
    m_post2expr.reset();
    m_parents.reset();
    m_doms.reset();
    m_tree.reset();
    m_root.reset();
}



// -----------------------
// dom_simplify_tactic

tactic * dom_simplify_tactic::translate(ast_manager & m) {
    return alloc(dom_simplify_tactic, m, m_simplifier->translate(m), m_params);
}

void dom_simplify_tactic::operator()(
    goal_ref const & in, 
    goal_ref_buffer & result, 
    model_converter_ref & mc, 
    proof_converter_ref & pc,
    expr_dependency_ref & core) {
    mc = 0; pc = 0; core = 0;

    tactic_report report("dom-simplify", *in.get());
    simplify_goal(*(in.get()));
    in->inc_depth();
    result.push_back(in.get());

}

void dom_simplify_tactic::cleanup() {
    m_trail.reset(); 
    m_args.reset(); 
    m_args2.reset(); 
    m_result.reset(); 
    m_dominators.reset(); 
}

expr_ref dom_simplify_tactic::simplify_ite(app * ite) {
    expr_ref r(m);
    expr * c = 0, * t = 0, * e = 0;
    VERIFY(m.is_ite(ite, c, t, e));
    unsigned old_lvl = scope_level();
    expr_ref new_c = simplify(c);
    if (m.is_true(new_c)) {
        r = simplify(t);
    }
    else if (m.is_false(new_c) || !assert_expr(new_c, false)) {
        r = simplify(e);
    }
    else {
        expr_ref new_t = simplify(t);
        pop(scope_level() - old_lvl);
        if (!assert_expr(new_c, true)) {
            return new_t;
        }
        expr_ref new_e = simplify(e);
        pop(scope_level() - old_lvl);
        if (c == new_c && t == new_t && e == new_e) {
            r = ite;
        }
        else if (new_t == new_e) {
            r = new_t;
        }
        else {
            TRACE("tactic", tout << new_c << "\n" << new_t << "\n" << new_e << "\n";);
            r = m.mk_ite(new_c, new_t, new_c);
        }        
    }    
    return r;
}

expr_ref dom_simplify_tactic::simplify(expr * e0) {
    expr_ref r(m);
    expr* e = 0;
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
    else {
        expr_dominators::tree_t const& t = m_dominators.get_tree();
        if (t.contains(e)) {
            ptr_vector<expr> const& children = t[e];
            for (expr * child : children) {
                simplify(child);
            }
        }
        if (is_app(e)) {
            m_args.reset();
            for (expr* arg : *to_app(e)) {
                m_args.push_back(get_cached(arg)); // TBD is cache really applied to all sub-terms?
            }
            r = m.mk_app(to_app(e)->get_decl(), m_args.size(), m_args.c_ptr());
        }
        else {
            r = e;
        }
    }
    (*m_simplifier)(r);
    cache(e0, r);
    TRACE("simplify", tout << "depth: " << m_depth << " " << mk_pp(e0, m) << " -> " << r << "\n";);
    --m_depth;
    return r;
}

expr_ref dom_simplify_tactic::simplify_and_or(bool is_and, app * e) {
    expr_ref r(m);
    unsigned old_lvl = scope_level();
    m_args.reset();
    for (expr * arg : *e) {
        r = simplify(arg);
        if (!assert_expr(r, !is_and)) {
            r = is_and ? m.mk_false() : m.mk_true();
        }
        m_args.push_back(r);
    }
    pop(scope_level() - old_lvl);
    m_args.reverse();
    m_args2.reset();
    for (expr * arg : m_args) {
        r = simplify(arg);
        if (!assert_expr(r, !is_and)) {
            r = is_and ? m.mk_false() : m.mk_true();
        }
        m_args2.push_back(r);
    }
    pop(scope_level() - old_lvl);
    m_args2.reverse();
    r = is_and ? mk_and(m_args2) : mk_or(m_args2);
    return r;
}


void dom_simplify_tactic::init(goal& g) {
    expr_ref_vector args(m);
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; ++i) args.push_back(g.form(i));
    expr_ref fml = mk_and(args);
    m_result.reset();
    m_trail.reset();
    m_dominators.compile(fml);
}

void dom_simplify_tactic::simplify_goal(goal& g) {

    SASSERT(scope_level() == 0);
    bool change = true;
    m_depth = 0;
    while (change) {
        change = false;

        // go forwards
        init(g);
        unsigned sz = g.size();
        for (unsigned i = 0; !g.inconsistent() && i < sz; ++i) {
            expr_ref r = simplify(g.form(i));
            if (i < sz - 1 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !g.proofs_enabled() && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            change |= r != g.form(i);
            proof* new_pr = 0;
            if (g.proofs_enabled()) {
                new_pr = m.mk_modus_ponens(g.pr(i), m.mk_rewrite_star(g.form(i), r, 0, 0)); 
            }
            g.update(i, r, new_pr, g.dep(i));
        }
        pop(scope_level());
        
        // go backwards
        init(g);
        sz = g.size();
        for (unsigned i = sz; !g.inconsistent() && i > 0; ) {
            --i;
            expr_ref r = simplify(g.form(i));
            if (i > 0 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !g.proofs_enabled() && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            change |= r != g.form(i);
            proof* new_pr = 0;
            if (g.proofs_enabled()) {
                new_pr = m.mk_modus_ponens(g.pr(i), m.mk_rewrite_star(g.form(i), r, 0, 0)); 
            }
            g.update(i, r, new_pr, g.dep(i));
        }
        pop(scope_level());
    }
    SASSERT(scope_level() == 0);
}


// ----------------------
// expr_substitution_simplifier

bool expr_substitution_simplifier::assert_expr(expr * t, bool sign) {
    expr* tt;    
    if (!sign) {
        update_substitution(t, 0);
    }
    else if (m.is_not(t, tt)) {
        update_substitution(tt, 0);
    }
    else {
        expr_ref nt(m.mk_not(t), m);
        update_substitution(nt, 0);
    }
    return true;
}


bool expr_substitution_simplifier::is_gt(expr* lhs, expr* rhs) {
    if (lhs == rhs) {
        return false;
    }
    if (m.is_value(rhs)) {
        return true;
    }
    SASSERT(is_ground(lhs) && is_ground(rhs));
    if (depth(lhs) > depth(rhs)) {
        return true;
    }
    if (depth(lhs) == depth(rhs) && is_app(lhs) && is_app(rhs)) {
        app* l = to_app(lhs);
        app* r = to_app(rhs);
        if (l->get_decl()->get_id() != r->get_decl()->get_id()) {
            return l->get_decl()->get_id() > r->get_decl()->get_id();
        }
        if (l->get_num_args() != r->get_num_args()) {
            return l->get_num_args() > r->get_num_args();
        }
        for (unsigned i = 0; i < l->get_num_args(); ++i) {
            if (l->get_arg(i) != r->get_arg(i)) {
                return is_gt(l->get_arg(i), r->get_arg(i));
            }
        }
        UNREACHABLE();
    }
    
    return false;
}

void expr_substitution_simplifier::update_substitution(expr* n, proof* pr) {
    expr* lhs, *rhs, *n1;
    if (is_ground(n) && (m.is_eq(n, lhs, rhs) || m.is_iff(n, lhs, rhs))) {
        compute_depth(lhs);
        compute_depth(rhs);
        if (is_gt(lhs, rhs)) {
            TRACE("propagate_values", tout << "insert " << mk_pp(lhs, m) << " -> " << mk_pp(rhs, m) << "\n";);
            m_scoped_substitution.insert(lhs, rhs, pr);
            return;
        }
        if (is_gt(rhs, lhs)) {
            TRACE("propagate_values", tout << "insert " << mk_pp(rhs, m) << " -> " << mk_pp(lhs, m) << "\n";);
            m_scoped_substitution.insert(rhs, lhs, m.mk_symmetry(pr));
            return;
        }
        TRACE("propagate_values", tout << "incompatible " << mk_pp(n, m) << "\n";);
    }
    if (m.is_not(n, n1)) {
        m_scoped_substitution.insert(n1, m.mk_false(), m.mk_iff_false(pr)); 
    }
    else {
        m_scoped_substitution.insert(n, m.mk_true(), m.mk_iff_true(pr)); 
    }
}

void expr_substitution_simplifier::compute_depth(expr* e) {
    ptr_vector<expr> todo;
    todo.push_back(e);    
    while (!todo.empty()) {
        e = todo.back();
        unsigned d = 0;
        if (m_expr2depth.contains(e)) {
            todo.pop_back();
            continue;
        }
        if (is_app(e)) {
            app* a = to_app(e);
            bool visited = true;
            for (expr* arg : *a) {
                unsigned d1 = 0;
                if (m_expr2depth.find(arg, d1)) {
                    d = std::max(d, d1);
                }
                else {
                    visited = false;
                    todo.push_back(arg);
                }
            }
            if (!visited) {
                continue;
            }
        }
        todo.pop_back();
        m_expr2depth.insert(e, d + 1);
    }
}
