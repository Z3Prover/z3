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
    void compute_dominators();
    void extract_tree();

public:
    expr_dominators(ast_manager& m): m(m), m_root(m) {}

    void compile(expr * e);
    void compile(unsigned sz, expr * const* es);
    tree_t const& get_tree() { return m_tree; }
    void reset();
    
};

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

        virtual simplifier * translate(ast_manager & m);

    };
private:
    ast_manager&         m;
    simplifier*          m_simplifier;
    params_ref           m_params;
    expr_ref_vector      m_trail, m_args, m_args2;
    obj_map<expr, expr*> m_result;
    expr_dominators      m_dominators;
    unsigned             m_scope_level;
    unsigned             m_depth;
    unsigned             m_max_depth;

    expr_ref simplify(expr* t);
    expr_ref simplify_ite(app * ite);
    expr_ref simplify_and(app * ite) { return simplify_and_or(true, ite); }
    expr_ref simplify_or(app * ite) { return simplify_and_or(false, ite); }
    expr_ref simplify_and_or(bool is_and, app * ite);
    void simplify_goal(goal& g);

    expr_ref get_cached(expr* t) { expr* r = 0; if (!m_result.find(r, r)) r = t; return expr_ref(r, m); }
    void cache(expr *t, expr* r) { m_result.insert(t, r); m_trail.push_back(r); }

    unsigned scope_level() { return m_scope_level; }
    void pop(unsigned n) { SASSERT(n <= m_scope_level); m_scope_level -= n; m_simplifier->pop(n); }
    bool assert_expr(expr* f, bool sign) { m_scope_level++; return m_simplifier->assert_expr(f, sign); }

    void init(goal& g);

public:
    dom_simplify_tactic(ast_manager & m, simplifier* s, params_ref const & p = params_ref()):
        m(m), m_simplifier(s), m_params(p), 
        m_trail(m), m_args(m), m_args2(m), 
        m_dominators(m), 
        m_scope_level(0), m_depth(0), m_max_depth(1024) {}


    virtual ~dom_simplify_tactic() {}

    virtual tactic * translate(ast_manager & m);
    virtual void updt_params(params_ref const & p) {}
    static  void get_param_descrs(param_descrs & r) {}
    virtual void collect_param_descrs(param_descrs & r) { get_param_descrs(r); }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core);

    virtual void cleanup();
};

class expr_substitution_simplifier : public dom_simplify_tactic::simplifier {
    ast_manager&             m;
    expr_substitution        m_subst;
    scoped_expr_substitution m_scoped_substitution;
    obj_map<expr, unsigned>  m_expr2depth;

    // move from asserted_formulas to here..
    void compute_depth(expr* e);
    bool is_gt(expr* lhs, expr* rhs);
    unsigned depth(expr* e) { return m_expr2depth[e]; }

public:
    expr_substitution_simplifier(ast_manager& m): m(m), m_subst(m), m_scoped_substitution(m_subst) {}
    virtual ~expr_substitution_simplifier() {}
    virtual bool assert_expr(expr * t, bool sign);

    void update_substitution(expr* n, proof* pr);
    
    virtual void operator()(expr_ref& r) { r = m_scoped_substitution.find(r); }
    
    virtual void pop(unsigned num_scopes) { m_scoped_substitution.pop(num_scopes); }
    
    virtual simplifier * translate(ast_manager & m) {
        SASSERT(m_subst.empty());
        return alloc(expr_substitution_simplifier, m);
    }

    
};

#endif
