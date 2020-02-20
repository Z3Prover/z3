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

#ifndef DOM_SIMPLIFY_TACTIC_H_
#define DOM_SIMPLIFY_TACTIC_H_

#include "ast/ast.h"
#include "ast/expr_substitution.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "util/obj_pair_hashtable.h"


class expr_dominators {
public:
    typedef obj_map<expr, ptr_vector<expr>> tree_t;
private:
    ast_manager&          m;
    expr_ref              m_root;
    obj_map<expr, unsigned>     m_expr2post; // reverse post-order number
    ptr_vector<expr>      m_post2expr;
    tree_t                m_parents;
    obj_map<expr, expr*>  m_doms;
    tree_t                m_tree;

    void add_edge(tree_t& tree, expr * src, expr* dst) {        
        tree.insert_if_not_there2(src, ptr_vector<expr>())->get_data().m_value.push_back(dst);        
    }

    void compute_post_order();
    expr* intersect(expr* x, expr * y);
    bool compute_dominators();
    void extract_tree();

    std::ostream& display(std::ostream& out, unsigned indent, expr* r);

public:
    expr_dominators(ast_manager& m): m(m), m_root(m) {}

    bool compile(expr * e);
    bool compile(unsigned sz, expr * const* es);
    tree_t const& get_tree() { return m_tree; }
    void reset();
    expr* idom(expr *e) const { return m_doms[e]; }

    std::ostream& display(std::ostream& out);
};

class dom_simplifier {
 public:
    dom_simplifier() {}
    
    virtual ~dom_simplifier() {}
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
    
    virtual dom_simplifier * translate(ast_manager & m) = 0;

    virtual unsigned scope_level() const = 0;
    
};

class dom_simplify_tactic : public tactic {
    ast_manager&         m;
    dom_simplifier*      m_simplifier;
    params_ref           m_params;
    expr_ref_vector      m_trail, m_args;
    obj_map<expr, expr*> m_result;
    expr_dominators      m_dominators;
    unsigned             m_depth;
    unsigned             m_max_depth;
    ptr_vector<expr>     m_empty;
    obj_pair_map<expr, expr, bool> m_subexpr_cache;
    bool                 m_forward;

    expr_ref simplify_rec(expr* t);
    expr_ref simplify_arg(expr* t);
    expr_ref simplify_ite(app * ite);
    expr_ref simplify_and(app * e) { return simplify_and_or(true, e); }
    expr_ref simplify_or(app * e) { return simplify_and_or(false, e); }
    expr_ref simplify_and_or(bool is_and, app * e);
    expr_ref simplify_not(app * e);
    void simplify_goal(goal& g);

    bool is_subexpr(expr * a, expr * b);

    expr_ref get_cached(expr* t) { expr* r = nullptr; if (!m_result.find(t, r)) r = t; return expr_ref(r, m); }
    void cache(expr *t, expr* r) { m_result.insert(t, r); m_trail.push_back(r); }
    void reset_cache() { m_result.reset(); }

    ptr_vector<expr> const & tree(expr * e);
    expr* idom(expr *e) const { return m_dominators.idom(e); }

    unsigned scope_level() { return m_simplifier->scope_level(); }
    void pop(unsigned n) { SASSERT(n <= m_simplifier->scope_level()); m_simplifier->pop(n); }
    bool assert_expr(expr* f, bool sign) { return m_simplifier->assert_expr(f, sign); }

    bool init(goal& g);

public:
    dom_simplify_tactic(ast_manager & m, dom_simplifier* s, params_ref const & p = params_ref()):
        m(m), m_simplifier(s), m_params(p), 
        m_trail(m), m_args(m), 
        m_dominators(m), m_depth(0), m_max_depth(1024), m_forward(true) {}

    ~dom_simplify_tactic() override;

    tactic * translate(ast_manager & m) override;
    void updt_params(params_ref const & p) override {}
    static  void get_param_descrs(param_descrs & r) {}
    void collect_param_descrs(param_descrs & r) override { get_param_descrs(r); }    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;
    void cleanup() override;
};

tactic * mk_dom_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
ADD_TACTIC("dom-simplify", "apply dominator simplification rules.", "mk_dom_simplify_tactic(m, p)")
*/

#endif
