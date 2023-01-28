/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dom_simplifier.cpp

Abstract:

    Dominator-based context simplifer.

Author:

    Nikolaj and Nuno 


--*/


#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/dom_simplifier.h"

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

    void updt_params(params_ref const & p) override {}

    void collect_param_descrs(param_descrs& r) override {}

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


dom_simplifier* mk_expr_substitution_simplifier(ast_manager& m) {
    return alloc(expr_substitution_simplifier, m);
}



