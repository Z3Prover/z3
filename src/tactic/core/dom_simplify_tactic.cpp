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
#include "ast/ast_ll_pp.h"
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

bool expr_dominators::compute_dominators() {
    expr * e = m_root;
    SASSERT(m_doms.empty());
    m_doms.insert(e, e);
    bool change = true;
    unsigned iterations = 1;
    while (change) {
        change = false;
        TRACE("simplify", 
              for (auto & kv : m_doms) {
                  tout << mk_bounded_pp(kv.m_key, m) << " |-> " << mk_bounded_pp(kv.m_value, m) << "\n";
              });

        SASSERT(m_post2expr.empty() || m_post2expr.back() == e);
        for (unsigned i = 0; i + 1 < m_post2expr.size(); ++i) {
            expr * child = m_post2expr[i];
            ptr_vector<expr> const& p = m_parents[child];
            expr * new_idom = nullptr, *idom2 = nullptr;

            for (expr * pred : p) {
                if (m_doms.contains(pred)) {
                    new_idom = !new_idom ? pred : intersect(new_idom, pred);
                }
            }
            if (!new_idom) {
                m_doms.insert(child, p[0]);
                change = true;
            }
            else if (!m_doms.find(child, idom2) || idom2 != new_idom) {
                m_doms.insert(child, new_idom);
                change = true;
            }
        }
        iterations *= 2;        
        if (change && iterations > m_post2expr.size()) {
            return false;
        }
    }
    return true;
}

void expr_dominators::extract_tree() {
    for (auto const& kv : m_doms) {
        add_edge(m_tree, kv.m_value, kv.m_key);
    }
}

bool expr_dominators::compile(expr * e) {
    reset();
    m_root = e;
    compute_post_order();
    if (!compute_dominators()) return false;
    extract_tree();
    TRACE("simplify", display(tout););
    return true;
}

bool expr_dominators::compile(unsigned sz, expr * const* es) {
    expr_ref e(m.mk_and(sz, es), m);
    return compile(e);
}

void expr_dominators::reset() {
    m_expr2post.reset();
    m_post2expr.reset();
    m_parents.reset();
    m_doms.reset();
    m_tree.reset();
    m_root.reset();
}

std::ostream& expr_dominators::display(std::ostream& out) {
    return display(out, 0, m_root);
}

std::ostream& expr_dominators::display(std::ostream& out, unsigned indent, expr* r) {
    for (unsigned i = 0; i < indent; ++i) out << " ";
    out << r->get_id() << ": " << mk_bounded_pp(r, m, 1) << "\n";
    if (m_tree.contains(r)) {
        for (expr* child : m_tree[r]) {
            if (child != r) 
                display(out, indent + 1, child);
        }
    }
    return out;
}


// -----------------------
// dom_simplify_tactic

dom_simplify_tactic::~dom_simplify_tactic() {
    dealloc(m_simplifier);
}

tactic * dom_simplify_tactic::translate(ast_manager & m) {
    return alloc(dom_simplify_tactic, m, m_simplifier->translate(m), m_params);
}

void dom_simplify_tactic::operator()(goal_ref const & in, goal_ref_buffer & result) {
    tactic_report report("dom-simplify", *in.get());
    simplify_goal(*(in.get()));
    in->inc_depth();
    result.push_back(in.get());
}

void dom_simplify_tactic::cleanup() {
    m_trail.reset();
    m_args.reset();
    m_result.reset();
    m_dominators.reset();
}

expr_ref dom_simplify_tactic::simplify_ite(app * ite) {
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
        
        pop(scope_level() - old_lvl);
        expr_ref new_t = simplify_arg(t);
        reset_cache();
        if (!assert_expr(new_c, true)) {
            return new_t;
        }
        for (expr * child : tree(ite)) 
            if (is_subexpr(child, e) && !is_subexpr(child, t)) 
                simplify_rec(child);
        pop(scope_level() - old_lvl);
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

expr_ref dom_simplify_tactic::simplify_arg(expr * e) {
    expr_ref r(m);    
    r = get_cached(e);
    (*m_simplifier)(r);
    CTRACE("simplify", e != r, tout << "depth: " << m_depth << " " << mk_pp(e, m) << " -> " << r << "\n";);
    return r;
}

/**
   \brief simplify e recursively.
*/
expr_ref dom_simplify_tactic::simplify_rec(expr * e0) {
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

expr_ref dom_simplify_tactic::simplify_and_or(bool is_and, app * e) {
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
            pop(scope_level() - old_lvl);                   
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
    
    pop(scope_level() - old_lvl);
    reset_cache();
    return { is_and ? mk_and(args) : mk_or(args), m };
}

expr_ref dom_simplify_tactic::simplify_not(app * e) {
    expr *ee;
    ENSURE(m.is_not(e, ee));
    unsigned old_lvl = scope_level();
    expr_ref t = simplify_rec(ee);
    pop(scope_level() - old_lvl);
    reset_cache();
    return mk_not(t);
}


bool dom_simplify_tactic::init(goal& g) {
    expr_ref_vector args(m);
    unsigned sz = g.size();
    for (unsigned i = 0; i < sz; ++i) args.push_back(g.form(i));
    expr_ref fml = mk_and(args);
    m_result.reset();
    m_trail.reset();
    return m_dominators.compile(fml);
}

void dom_simplify_tactic::simplify_goal(goal& g) {

    SASSERT(scope_level() == 0);
    bool change = true;
    unsigned n  = 0;
    m_depth = 0;
    while (change && n < 10) {
        change = false;
        ++n;

        // go forwards
        m_forward = true;
        if (!init(g)) return;
        unsigned sz = g.size();
        for (unsigned i = 0; !g.inconsistent() && i < sz; ++i) {
            expr_ref r = simplify_rec(g.form(i));
            if (i < sz - 1 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !g.proofs_enabled() && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            CTRACE("simplify", r != g.form(i), tout << r << " " << mk_pp(g.form(i), m) << "\n";);
            change |= r != g.form(i);
            proof_ref new_pr(m);
            if (g.proofs_enabled() && g.pr(i)) {
                new_pr = m.mk_modus_ponens(g.pr(i), m.mk_rewrite(g.form(i), r));
            }
            g.update(i, r, new_pr, g.dep(i));
        }
        pop(scope_level());

        // go backwards
        m_forward = false;
        if (!init(g)) return;
        sz = g.size();
        for (unsigned i = sz; !g.inconsistent() && i > 0; ) {
            --i;
            expr_ref r = simplify_rec(g.form(i));
            if (i > 0 && !m.is_true(r) && !m.is_false(r) && !g.dep(i) && !g.proofs_enabled() && !assert_expr(r, false)) {
                r = m.mk_false();
            }
            change |= r != g.form(i);
            CTRACE("simplify", r != g.form(i), tout << r << " " << mk_pp(g.form(i), m) << "\n";);
            proof_ref new_pr(m);
            if (g.proofs_enabled() && g.pr(i)) {
                new_pr = m.mk_rewrite(g.form(i), r);
                new_pr = m.mk_modus_ponens(g.pr(i), new_pr);
            }
            g.update(i, r, new_pr, g.dep(i));
        }
        pop(scope_level());
    }
    SASSERT(scope_level() == 0);
}

/**
   \brief determine if a is dominated by b. 
   Walk the immediate dominators of a upwards until hitting b or a term that is deeper than b.
   Save intermediary results in a cache to avoid recomputations.
*/

bool dom_simplify_tactic::is_subexpr(expr * a, expr * b) {
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

ptr_vector<expr> const & dom_simplify_tactic::tree(expr * e) {
    if (auto p = m_dominators.get_tree().find_core(e))
        return p->get_data().get_value();
    return m_empty;
}


// ---------------------
// expr_substitution_simplifier
namespace {

class expr_substitution_simplifier : public dom_simplifier {
    ast_manager&             m;
    expr_substitution        m_subst;
    scoped_expr_substitution m_scoped_substitution;
    obj_map<expr, unsigned>  m_expr2depth;
    expr_ref_vector          m_trail;

    // move from asserted_formulas to here..
    void compute_depth(expr* e) {
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

    bool is_gt(expr* lhs, expr* rhs) {
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

    unsigned depth(expr* e) { return m_expr2depth[e]; }

public:
    expr_substitution_simplifier(ast_manager& m): m(m), m_subst(m), m_scoped_substitution(m_subst), m_trail(m) {}
    ~expr_substitution_simplifier() override {}

    bool assert_expr(expr * t, bool sign) override {
        expr* tt;
        if (m.is_not(t, tt))
            return assert_expr(tt, !sign);
        if (m.is_false(t))
            return sign;
        if (m.is_true(t))
            return !sign;

        TRACE("simplify", tout << t->get_id() << ": " << mk_bounded_pp(t, m) << " " << (sign?" - neg":" - pos") << "\n";);

        m_scoped_substitution.push();
        if (!sign) {
            update_substitution(t, nullptr);
        }
        else {
            expr_ref nt(m.mk_not(t), m);
            update_substitution(nt, nullptr);
        }
        return true;
    }

    void update_substitution(expr* n, proof* pr) {
        expr* lhs, *rhs, *n1;
        if (is_ground(n) && m.is_eq(n, lhs, rhs)) {
            compute_depth(lhs);
            compute_depth(rhs);
            m_trail.push_back(lhs);
            m_trail.push_back(rhs);
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

    void operator()(expr_ref& r) override { r = m_scoped_substitution.find(r); }

    void pop(unsigned num_scopes) override { m_scoped_substitution.pop(num_scopes); }

    unsigned scope_level() const override { return m_scoped_substitution.scope_level(); }

    dom_simplifier * translate(ast_manager & m) override {
        SASSERT(m_subst.empty());
        return alloc(expr_substitution_simplifier, m);
    }
};
}

tactic * mk_dom_simplify_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(dom_simplify_tactic, m, alloc(expr_substitution_simplifier, m), p));
}
