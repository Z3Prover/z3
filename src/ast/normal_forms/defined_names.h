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

/**
   \brief Mapping from expressions to skolem functions that are used to name them.

   The mapping supports backtracking using the methods #push_scope and #pop_scope.
*/
class defined_names {
    struct impl;
    struct pos_impl;
    impl      * m_impl;
    pos_impl  * m_pos_impl;
public:
    defined_names(ast_manager & m, char const * fresh_prefix = "z3name");
    ~defined_names();

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
    bool mk_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr);

    /**
       \brief Create a name for a positive occurrence of the expression \c e.
       
       Return true if a new pos-name was created, and false if a pos-name already exists for \c e.

       If true is returned, then the definition of the new name is stored into new_def.
       It has the form:  (or (not n) e)

       Remark: the definitions are closed with an universal quantifier if e contains free variables.
    */
    bool mk_pos_name(expr * e, expr_ref & new_def, proof_ref & new_def_pr, app_ref & n, proof_ref & pr);

    void push();
    void pop(unsigned num_scopes);
    void reset();

    unsigned get_num_names() const;
    func_decl * get_name_decl(unsigned i) const;
};

#endif /* _DEFINED_NAMES_H_ */

