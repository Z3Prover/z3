/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    substitution_tree.h

Abstract:

    Substitution Trees 

Author:

    Leonardo de Moura (leonardo) 2008-02-03.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/substitution/substitution.h"

/**
   \brief Substitution tree visitor.
*/
class st_visitor {
protected:
    substitution & m_subst;
public:
    st_visitor(substitution & s):m_subst(s) {}
    virtual ~st_visitor() {}
    substitution & get_substitution() { return m_subst; }
    virtual bool operator()(expr * e) { return true; }
};

/**
   \brief Substitution tree term index.
*/
class substitution_tree {
    
    typedef std::pair<var *, expr *> subst;

    struct node {
        bool   m_leaf;
        svector<subst>   m_subst;
        node *           m_next_sibling;
        union {
            node *           m_first_child;
            expr *           m_expr;
        };
        node(bool leaf):m_leaf(leaf), m_next_sibling(nullptr), m_first_child(nullptr) {}
    };

    ast_manager &     m_manager;
    ptr_vector<node>  m_roots;
    unsigned          m_max_reg;
    ptr_vector<expr>  m_registers;
    unsigned          m_size;
    ptr_vector<var_ref_vector> m_vars; // mapping from decl_id to var_ref_vector

    // Compilation time fields
    unsigned          m_next_reg;
    bit_vector        m_used_regs;
    unsigned_vector   m_todo;
    svector<subst>    m_compatible;
    svector<subst>    m_incompatible;
    
    // Execution time fields
    substitution *    m_subst;
    ptr_vector<node>  m_bstack;
    unsigned          m_in_offset;
    unsigned          m_st_offset;
    unsigned          m_reg_offset;
    typedef std::pair<expr_offset, expr_offset> entry;
    svector<entry>    m_visit_todo;

    unsigned next_reg();
    void push(svector<subst> & sv, subst const & s);
    expr * get_reg_value(unsigned ridx);
    void set_reg_value(unsigned ridx, expr * e);
    void erase_reg_from_todo(unsigned ridx);

    void linearize(svector<subst> & result);
    void process_args(app * in, app * out);
    void reset_registers(unsigned old_size);
    unsigned get_compatibility_measure(svector<subst> const & sv);
    node * find_best_child(node * r);
    void reset_compiler();
    node * mk_node_for(expr * new_expr);
    void mark_used_reg(unsigned ridx);
    void mark_used_regs(svector<subst> const & sv);

    bool is_fully_compatible(svector<subst> const & sv);
    bool find_fully_compatible_child(node * r, node * & prev, node * & child);
    static bool at_least_3_children(node * r);
    void delete_node(node * n);

    void display(std::ostream & out, subst const & s) const;
    void display(std::ostream & out, svector<subst> const & sv) const;
    void display(std::ostream & out, node * n, unsigned delta) const;

    enum st_visit_mode {
        STV_UNIF,
        STV_INST,
        STV_GEN
    };

    expr_offset find(expr_offset p);
    bool backtrack();
    
    template<st_visit_mode Mode>
    bool bind_var(var * v, unsigned offset, expr_offset const & p);
    template<st_visit_mode Mode>
    bool unify_match(expr_offset p1, expr_offset p2);
    template<substitution_tree::st_visit_mode Mode>
    bool visit_vars(expr * e, st_visitor & st);
    template<st_visit_mode Mode>
    bool visit(svector<subst> const & s);
    template<st_visit_mode Mode>
    bool visit(expr * e, st_visitor & st, node * r);
    template<st_visit_mode Mode>
    void visit(expr * e, st_visitor & st, unsigned in_offset, unsigned st_offset, unsigned reg_offset);

    void clear_stack();

public:
    substitution_tree(ast_manager & m);
    ~substitution_tree();

    void insert(app * n);
    void insert(expr * n);
    void erase(app * n);
    void erase(expr * n);
    void reset();
    
    bool empty() const { return m_size == 0; }

    void unify(expr * e, st_visitor & v, unsigned in_offset = 0, unsigned st_offset = 1, unsigned reg_offset = 2);
    void inst(expr * e, st_visitor & v, unsigned in_offset = 0, unsigned st_offset = 1, unsigned reg_offset = 2);
    void gen(expr * e, st_visitor & v, unsigned in_offset = 0, unsigned st_offset = 1, unsigned reg_offset = 2);

    unsigned get_approx_num_regs() const { return m_max_reg + 1; }

    void display(std::ostream & out) const;
};


