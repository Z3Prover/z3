/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    name_exprs.h

Abstract:

    Goodies for naming nested expressions.

Author:

    Leonardo (leonardo) 2011-10-06

Notes:

--*/
#ifndef NAME_EXPRS_H_
#define NAME_EXPRS_H_

#include"ast.h"
#include"defined_names.h"

class expr_predicate {
public:
    virtual bool operator()(expr * t) = 0;
};

class name_exprs {
public:
    virtual ~name_exprs() {}
    virtual void operator()(expr * n,                          // [IN] expression that contain the sub-expressions to be named
                            expr_ref_vector & new_defs,        // [OUT] new definitions
                            proof_ref_vector & new_def_proofs, // [OUT] proofs of the new definitions 
                            expr_ref & r,                      // [OUT] resultant expression
                            proof_ref & p                      // [OUT] proof for (iff n p)
                            ) = 0;
    
    virtual void set_cancel(bool f) = 0;
    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }
    virtual void reset() = 0;
};

/**
   \brief Create an expression "namer" that will create replace nested expressions that satisfy pred with new
   fresh declarations.
*/
name_exprs * mk_expr_namer(ast_manager & m, defined_names & n, expr_predicate & pred);

/**
   \brief Create an expression "namer" that will replace quantifiers and labels with new fresh declarations.
*/
name_exprs * mk_quantifier_label_namer(ast_manager & m, defined_names & n);

/**
   \brief Create an expression "namer" that will replace all nested formulas and term if-then-elses with 
   fresh declarations.
*/
name_exprs * mk_nested_formula_namer(ast_manager & m, defined_names & n);

void del_name_exprs(name_exprs * functor);

#endif
