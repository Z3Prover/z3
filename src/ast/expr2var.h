/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr2var.h

Abstract:

    The mapping between Z3 expressions and (low level) variables.
    Example of low level variables:
       - SAT solver
       - Polynomial 
       - etc.

Author:

    Leonardo (leonardo) 2011-12-23

Notes:

--*/
#ifndef EXPR2VAR_H_
#define EXPR2VAR_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"

/**
   \brief The mapping between Z3 expressions and (low level) variables.
*/
class expr2var {
public:
    typedef unsigned var;
    typedef obj_map<expr, var>::key_data key_value;
    typedef key_value const* iterator;
    typedef ptr_vector<expr>::const_iterator recent_iterator;
protected:
    ast_manager &    m_manager;
    
    unsigned_vector    m_id2map;
    svector<key_value> m_mapping;
    ptr_vector<expr> m_recent_exprs;
    unsigned_vector  m_recent_lim;
    bool             m_interpreted_vars;
public:
    expr2var(ast_manager & m);
    ~expr2var();

    ast_manager & m() const { return m_manager; }

    void insert(expr * n, var v);
    
    var to_var(expr * n) const;
    
    bool is_var(expr * n) const { return m_id2map.get(n->get_id(), UINT_MAX) != UINT_MAX; }

    void display(std::ostream & out) const;
    
    void mk_inv(expr_ref_vector & var2expr) const;

    // return true if the mapping contains interpreted vars.
    bool interpreted_vars() const { return m_interpreted_vars; }
    
    iterator begin() const { return m_mapping.begin(); }
    iterator end() const { return m_mapping.end(); }

    void reset_recent() { SASSERT(m_recent_lim.empty()); m_recent_exprs.reset(); }

    // Iterators for traversing the recently registered expressions.
    // The set of recent registered expressions is reset by using reset_recent().
    recent_iterator begin_recent() const { return m_recent_exprs.begin(); }
    recent_iterator end_recent() const { return m_recent_exprs.end(); }
    
    void reset();

    void push();
    void pop(unsigned num_scopes);
};

#endif
