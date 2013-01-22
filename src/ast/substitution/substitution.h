/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    substitution.h

Abstract:

    A substitution, that is, a mapping from (variable, offset) to (expr, offset).
    We use offsets in order to avoid creating variants of terms.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

    nbjorner 2013-01-21:
      - reset the apply cache on pop_scope to make sure that popped
        substitutions are invalidated.
      - reset_cache if a new binding was added after application
        of a substitution.
      - Add m_refs to make sure terms in the range of the 
        substitution have the same life-time as the substitution.
      - Remove reset_subst() function. If called without resetting the cache, then
        results of applying substitutions are incoherent.
      - Replace UNREACHABLE segment for quantifiers by recursive invocation of substitution
        that updates expressions within quantifiers. It shifts all variables in the domain
        of the current substitution by the number of quantified variables.

--*/
#ifndef _SUBSTITUTION_H_
#define _SUBSTITUTION_H_

#include"expr_offset_map.h"
#include"var_offset_map.h"
#include"ast_pp.h"

/**
   \brief A mapping from (variable,offset) to expr_offset.
*/
class substitution {
    ast_manager &               m_manager;
    var_offset_map<expr_offset> m_subst;

    // field for backtracking
    typedef std::pair<unsigned, unsigned> var_offset;
    svector<var_offset>         m_vars;
    expr_ref_vector             m_refs;
    unsigned_vector             m_scopes;

    // fields for applying substitutions
    svector<expr_offset>        m_todo;
    expr_offset_map<expr *>     m_apply_cache;
    expr_ref_vector             m_new_exprs;

    // fields for checking for cycles
    enum color { White, Grey, Black };
    expr_offset_map<color>      m_color;


    // keep track of how substitution state was last updated.
    enum state { CLEAN, APPLY, INSERT };
    state                       m_state;

#ifdef Z3DEBUG
    unsigned                    m_max_offset_since_reset;
#endif 
    void apply_visit(expr_offset const & n, bool & visited);


    color get_color(expr_offset const & p) const;
    void set_color(expr_offset const & p, color c);
    
    void visit(expr_offset const & p, bool & visited);
    bool visit_children(expr_offset const & p);
    bool acyclic(expr_offset p);

public:
    substitution(ast_manager & m);
    ast_manager & get_manager() const { return m_manager; }

    // -----------------------------------
    //
    // Reserve memory for the given number of 
    // offsets and variables.
    //
    // -----------------------------------

    void reserve(unsigned num_offsets, unsigned num_vars) { m_subst.reserve(num_offsets, num_vars); }
    void reserve_offsets(unsigned num_offsets) { m_subst.reserve_offsets(num_offsets); }
    void reserve_vars(unsigned num_vars) { m_subst.reserve_vars(num_vars); }

    // -----------------------------------
    //
    // Reset functions
    //
    // -----------------------------------

    // reset everything
    void reset();
    // reset only the substitution application cache
    void reset_cache();

    // -----------------------------------
    //
    // Backtracking
    //
    // -----------------------------------

    void push_scope() { m_scopes.push_back(m_vars.size()); }
    void pop_scope(unsigned num_scopes = 1);
    unsigned get_scope_lvl() { return m_scopes.size(); }
    bool top_scope_has_bindings() const { return m_scopes.empty() ? !m_vars.empty() : m_scopes.back() < m_vars.size(); }
    unsigned get_num_bindings() const { return m_vars.size(); }
    

    // -----------------------------------
    //
    // Cycle detection
    //
    // -----------------------------------

    bool acyclic();

    // -----------------------------------
    //
    // Insertion & Lookup
    // 
    // get_binding supplies a way to inspect the substitution.
    //
    // -----------------------------------

    void insert(unsigned v_idx, unsigned offset, expr_offset const & t) {
        TRACE("subst_insert", tout << "inserting: #" << v_idx << ":" << offset << " --> " << mk_pp(t.get_expr(), m_manager)
              << ":" << t.get_offset() << "\n";);
        m_vars.push_back(var_offset(v_idx, offset));
        m_refs.push_back(t.get_expr());
        m_subst.insert(v_idx, offset, t);
        m_state = INSERT;
    }
    void insert(var * v, unsigned offset, expr_offset const & t) { insert(v->get_idx(), offset, t); }
    void insert(expr_offset v, expr_offset const & t) {
        SASSERT(is_var(v.get_expr()));
        insert(to_var(v.get_expr()), v.get_offset(), t);
    }

    bool find(unsigned v_idx, unsigned offset, expr_offset & r) const { return m_subst.find(v_idx, offset, r); }
    bool find(var * v, unsigned offset, expr_offset & r) const { return find(v->get_idx(), offset, r); }
    bool find(expr_offset v, expr_offset & r) const { 
        SASSERT(is_var(v.get_expr()));
        return find(to_var(v.get_expr()), v.get_offset(), r);
    }

    void get_binding(unsigned binding_num, var_offset& var, expr_offset& r) {
        var = m_vars[binding_num];
        VERIFY(m_subst.find(var.first, var.second, r));
    }

    bool contains(var * v, unsigned offset) { expr_offset r; return find(v, offset, r); }

    // -----------------------------------
    //
    // Application
    //
    // -----------------------------------
    
    /**
       \brief Apply the current substitution to the given
       expression+offset. The result is an expression.
       
       The argument num_actual_offsets is the maximum offset used in a
       insert method since the last reset.
       
       The argument deltas is an array of size num_actual_offsets. It contains
       the variable delta for each offset. A free variable x:i in an expression offset t:j is mapped
       to the variable x+delta[i]. 
    */
    void apply(unsigned num_actual_offsets, unsigned const * deltas, expr_offset const & n, expr_ref & result) {
        apply(num_actual_offsets, deltas, n, expr_offset(0, 0), expr_offset(0, 0), result);
    }
    
    /**
       \brief Similar to the previous method, but occurrences of s in n are substituted by t.
       If s != expr_offset(0,0), then the cache is reset before and after the execution of this procedure.
    */
    void apply(unsigned num_actual_offsets, unsigned const* deltas, expr_offset const & n, expr_offset const & s, expr_offset const & t, expr_ref & result);

    void apply(expr * n, expr_ref & result) {
        unsigned deltas[1] = { 0 };
        apply(1, deltas, expr_offset(n, 0), result);
    }

    // -----------------------------------
    //
    // Debugging
    //
    // -----------------------------------
 
    /**
       \brief Dump the current substitution (for debugging purposes).
    */
    void display(std::ostream & out, unsigned num_actual_offsets, unsigned const * deltas);

    /**
       \brief Dump the current substitution without normalizing expressions (for debugging purposes).
    */
    void display(std::ostream & out);

    
    // -----------------------------------
    //
    // Compare terms modulo a substitution
    //
    // -----------------------------------
    bool compare(expr_offset t1, expr_offset t2);

};

#endif
