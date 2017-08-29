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

#if 0

#include "ast/ast.h"

class expr_dominators {
public:
    typedef obj_map<expr, ptr_vector<expr>> tree_t;
private:
    ast_manager&          m;
    expr_ref              m_root;
    obj_map<unsigned>     m_expr2post; // reverse post-order number
    ptr_vector<expr>      m_post2expr;
    tree_t                m_parents;
    obj_map<expr, expr*>  m_doms;
    tree_t                m_tree;

    void add_edge(tree_t& tree, expr * src, expr* dst) {        
        tree.insert_if_not_there(src, ptr_vector<expr>()).push_back(dst);        
    }

    /**
       \brief compute a post-order traversal for e.
       Also populate the set of parents
     */
    void compute_post_order() {
        unsigned post_num = 0;
        SASSERT(m_post2expr.empty());
        SASSERT(m_expr2post.empty());
        ast_mark mark;
        ptr_vector<expr> todo;
        todo.push_back(m_root);
        while (!todo.empty()) {
            expr* e = todo.back();
            if (is_marked(e)) {
                todo.pop_back();
                continue;
            }
            if (is_app(e)) {
                app* a = to_app(e);
                bool done = true;
                for (expr* arg : *a) {
                    if (!is_marked(arg)) {
                        todo.push_back(arg);
                        done = false;
                    }
                }
                if (done) {
                    mark.mark(e);
                    m_expr2post.insert(e, post_num++);
                    m_post2expr.push_back(e);
                    todo.pop_back();
                    for (expr* arg : *a) {
                        add_edge(m_parents, a, arg);
                    }
                }
            }
            else {
                todo.pop_back();
            }
        }
    }

    expr* intersect(expr* x, expr * y) {
        unsigned n1 = m_expr2post[x];
        unsigned n2 = m_expr2post[y];
        while (n1 != n2) {
            if (n1 < n2)
                n1 = m_doms[n1];
            else if (n1 > n2)
                n2 = m_doms[n2];
        }
        return n1;
    }

    void compute_dominators() {
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
                }
            }
        }
    }

    void extract_tree() {
        for (auto const& kv : m_doms) {
            expr * child = kv.m_key;
            for (expr * parent : kv.m_value) {
                add_edge(m_tree, parent, child);
            }
        }
    }    

    void reset() {
        m_expr2post.reset();
        m_post2expr.reset();
        m_parents.reset();
        m_doms.reset();
        m_tree.reset();
        m_root.reset();
    }


public:
    expr_dominators(ast_manager& m): m(m), m_root(m) {}

    void compile(expr * e) {
        reset();
        m_root = e;
        compute_post_order();
        compute_dominators();
        extract_tree();
    }

    void compile(unsigned sz, expr * const* es) {
        expr_ref e(m.mk_and(sz, es), m);
        compile(e);
    }

    tree_t const& get_tree() { return m_tree; }

};

// goes to header file:

class dom_simplify_tactic : public tactic {
public:
    class simplifier {
    public:
        virtual ~simplifier() {}
        /**
           \brief assert_expr performs an implicit push
         */
        virtual bool assert_expr(expr * t, bool sign) = 0;

        /**
           \brief apply simplification.
        */
        virtual void operator()(expr_ref& r) = 0;

        /**
           \brief pop scopes accumulated from assertions.
         */
        virtual void pop(unsigned num_scopes) = 0;
    };
private:
    simplifier&          m_simplifier;
    params_ref           m_params;
    expr_ref_vector      m_trail;
    obj_map<expr, expr*> m_result;
    expr_dominators      m_dominators;

    expr_ref simplify(expr* t);
    expr_ref simplify_ite(app * ite);
    expr_ref simplify_and(app * ite) { return simplify_and_or(true, ite); }
    expr_ref simplify_or(app * ite) { return simplify_and_or(false, ite); }
    expr_ref simplify_and_or(bool is_and app * ite);

    expr_ref get_cache(expr* t) { if (!m_result.find(r, r)) r = t; return expr_ref(r, m); }
    void cache(expr *t, expr* r) { m_result.insert(t, r); m_trail.push_back(r); }

    void simplify_goal(goal_ref& g);

public:
    dom_simplify_tactic(ast_manager & m, simplifier& s, params_ref const & p = params_ref());

    virtual tactic * translate(ast_manager & m);

    virtual ~dom_simplify_tactic();

    virtual void updt_params(params_ref const & p);
    static  void get_param_descrs(param_descrs & r);
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core);

    virtual void cleanup();
};

// implementation:

expr_ref dom_simplifier_tactic::simplify_ite(app * ite) {
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
        expr_ref t = simplify(t);
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

expr_ref dom_simplifier_tactic::simplify(expr * e0) {
    expr_ref r(m);
    expr* e = 0;
    if (!m_result.find(e0, e)) {
        e = e0;
    }

    if (m.is_ite(e)) {
        r = simplify_ite(to_app(e));
    }
    else if (m.is_and(e)) {
        r = simplify_and(to_app(e));
    }
    else if (m.is_or(e)) {
        r = simplify_or(to_app(e));
    }
    else {
        tree_t const& t = m_dominators.get_tree();
        if (t.contains(e)) {
            ptr_vector<expr> const& children = t[e];
            for (expr * child : children) {
                simplify(child);
            }
        }
        if (is_app(e)) {
            m_args.reset();
            for (expr* arg : *to_app(e)) {
                m_args.push_back(get_cached(arg));
            }
            r = m.mk_app(to_app(e)->get_decl(), m_args.size(), m_args.c_ptr());
        }
        else {
            r = e;
        }
    }
    m_simplifier(r);
    cache(e0, r);
    return r;
}

expr_ref dom_simplifier_tactic::simplify_or_and(bool is_and, app * e) {
    expr_ref r(m);
    unsigned old_lvl = scope_level();
    m_args.reset();
    for (expr * arg : *e) {
        r = simplify(arg);
        if (!assert_expr(r, is_and)) {
            r = is_and ? m.mk_false() : m.mk_true();
        }
        m_args.push_back(r);
    }
    pop(scope_level() - old_lvl);
    m_args.reverse();
    m_args2.reset();
    for (expr * arg : m_args) {
        r = simplify(arg);
        if (!assert_expr(r, is_and)) {
            r = is_and ? m.mk_false() : m.mk_true();
        }
        m_args2.push_back(r);
    }
    pop(scope_level() - old_lvl);
    m_args2.reverse();
    r = is_and ? mk_and(m_args2) : mk_or(m_args2);
    return r;
}

void dom_simplifier_tactic::simplify_goal(goal& g) {
    expr_ref_vector args(m);
    expr_ref fml(m);
    for (unsigned i = 0; i < sz; ++i) args.push_back(g.form(i));
    fml = mk_and(args);
    expr_ref tmp(fml);
    // TBD: deal with dependencies.
    do {
        m_result.reset();
        m_trail.reset();
        m_dominators.compile(fml);
#if 0
        for (unsigned i = 0; i < sz; ++i) {
            r = simplify(g.form(i));
            // TBD: simplfy goal as a conjuction ?
            //
        }
#endif
        tmp = fml;
        fml = simplify(fml);
    }
    while (tmp != fml);
    //g.reset();
    //g.add(fml);
}


#endif
