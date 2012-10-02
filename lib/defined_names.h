/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    defined_names.h

Abstract:

    In some transformations, we need to name expressions.
    These expressions are stored in a table.

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#ifndef _DEFINED_NAMES_H_
#define _DEFINED_NAMES_H_

#include"ast.h"
#include"obj_hashtable.h"

/**
   \brief Mapping from expressions to skolem functions that are used to name them.

   The mapping supports backtracking using the methods #push_scope and #pop_scope.
*/
class defined_names {

    struct impl {
        typedef obj_map<expr, app *>   expr2name;
        typedef obj_map<expr, proof *> expr2proof;
        ast_manager &    m_manager;
        symbol           m_z3name;
        
        /**
           \brief Mapping from expressions to their names. A name is an application.
           If the expression does not have free variables, then the name is just a constant.
        */
        expr2name        m_expr2name;
        /**
           \brief Mapping from expressions to the apply-def proof.
           That is, for each expression e, m_expr2proof[e] is the
           proof e and m_expr2name[2] are observ. equivalent.
           
           This mapping is not used if proof production is disabled.
        */
        expr2proof       m_expr2proof;
        
        /**
           \brief Domain of m_expr2name. It is used to keep the expressions
           alive and for backtracking
        */
        expr_ref_vector  m_exprs; 
        expr_ref_vector  m_names;        //!< Range of m_expr2name. It is used to keep the names alive.
        proof_ref_vector m_apply_proofs; //!< Range of m_expr2proof. It is used to keep the def-intro proofs alive.
        
        
        unsigned_vector m_lims;          //!< Backtracking support.

        impl(ast_manager & m, char const * prefix);
        virtual ~impl();

        app * gen_name(expr * e, sort_ref_buffer & var_sorts, buffer<symbol> & var_names);
        void cache_new_name(expr * e, app * name);
        void cache_new_name_intro_proof(expr * e, proof * pr);
        void bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref & result);
        void bound_vars(sort_ref_buffer const & sorts, buffer<symbol> const & names, expr * def_conjunct, app * name, expr_ref_buffer & result);
        virtual void mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> const & var_names, expr_ref & new_def);
        bool mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr);
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void reset();
    };

    struct pos_impl : public impl {
        pos_impl(ast_manager & m, char const * fresh_prefix):impl(m, fresh_prefix) {}
        virtual void mk_definition(expr * e, app * n, sort_ref_buffer & var_sorts, buffer<symbol> const & var_names, expr_ref & new_def);
    };
    
    impl      m_impl;
    pos_impl  m_pos_impl;
public:
    defined_names(ast_manager & m, char const * fresh_prefix = "z3name"):m_impl(m, fresh_prefix), m_pos_impl(m, fresh_prefix) {}

    // -----------------------------------
    //
    // High-level API
    //
    // -----------------------------------

    /**
       \brief Create a name for expression \c e if it doesn't already exists. 
       
       Return true if a new name was created, and false if a name already exists for \c e.

       The resultant new name is stored in n, and a [apply-def] proof
       that (= e n) is stored into pr.

       If true is returned, then the definition of the new name is
       stored into new_def, and a [def-intro] proof into new_def_pr.

       The proofs are not produced when proof generation is disabled.

       The definition of an expression e with name n is:

       - (and (or (not e) n) (or e (not n)))  if e is an formula.
       - (and (or (not c) (= n t1)) (or c (= n t2))) if e is an if-then-else term of the form (ite c t1 t2)
       - (= n e) if e is a term.

       Remark: the definitions are closed with an universal quantifier if e contains free variables.
    */
    bool mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr) {
        return m_impl.mk_name(e, new_def, new_def_pr, n, pr);
    }

    /**
       \brief Create a name for a positive occurrence of the expression \c e.
       
       Return true if a new pos-name was created, and false if a pos-name already exists for \c e.

       If true is returned, then the definition of the new name is stored into new_def.
       It has the form:  (or (not n) e)

       Remark: the definitions are closed with an universal quantifier if e contains free variables.
    */
    bool mk_pos_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr) {
        return m_pos_impl.mk_name(e, new_def, new_def_pr, n, pr);
    }

    void push_scope() {
        m_impl.push_scope();
        m_pos_impl.push_scope();
    }

    void pop_scope(unsigned num_scopes) {
        m_impl.pop_scope(num_scopes);
        m_pos_impl.pop_scope(num_scopes);
    }

    void reset() {
        m_impl.reset();
        m_pos_impl.reset();
    }
};

#endif /* _DEFINED_NAMES_H_ */

