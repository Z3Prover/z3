/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dom_simplifier.h

Abstract:

    Dominator-based context simplifer.

Author:

    Nikolaj and Nuno 

--*/

#pragma once

#include "ast/ast.h"
#include "ast/expr_substitution.h"
#include "util/obj_pair_hashtable.h"

class expr_dominators {
public:
    typedef obj_map<expr, ptr_vector<expr>> tree_t;
private:
    ast_manager&            m;
    expr_ref                m_root;
    obj_map<expr, unsigned> m_expr2post; // reverse post-order number
    ptr_vector<expr>        m_post2expr;
    tree_t                  m_parents;
    obj_map<expr, expr*>    m_doms;
    tree_t                  m_tree;

    void add_edge(tree_t& tree, expr * src, expr* dst) {        
        tree.insert_if_not_there(src, ptr_vector<expr>()).push_back(dst);
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
    virtual ~dom_simplifier() = default;
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

    virtual void updt_params(params_ref const & p) = 0; 

    virtual void collect_param_descrs(param_descrs& r) = 0;
};

dom_simplifier* mk_expr_substitution_simplifier(ast_manager& m);
