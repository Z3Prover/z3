/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    quant_hoist.h

Abstract:

    Quantifier hoisting utility.

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

    Hoisted from quant_elim.

--*/

#ifndef QUANTIFIER_HOISTER_H_
#define QUANTIFIER_HOISTER_H_

#include "ast.h"

class quantifier_hoister {
    class impl;
    impl* m_impl;
public:
    quantifier_hoister(ast_manager& m);
    
    ~quantifier_hoister(); 

    /**
       \brief Pull top-most quantifier up.
       Create fresh constants for the bound variables.
       Return the constants, the quantifier type (forall or exists), and
       the sub-formula under the quantifier.

       The list of variables is empty if the formula is quantifier free or
       if the existing quantifiers occur under a connective other than
       or, and, implies, ite (then and else branch only).
    */

    void operator()(expr* fml, app_ref_vector& vars, bool& is_fa, expr_ref& result);

    /**
       \brief Pull top-most existential quantifier up.

       The list of variables is empty if there are no top-level existential quantifier.
    */
    void pull_exists(expr* fml, app_ref_vector& vars, expr_ref& result);


    /**
       \brief Pull top-most universal (is_forall=true) or existential (is_forall=false) quantifier up.

       The list of variables is empty if there are no top-level universal/existential quantifier.
    */
    void pull_quantifier(bool is_forall, expr_ref& fml, app_ref_vector& vars);

    /**
       \brief Pull top-most universal (is_forall true) or existential (is_forall=false) quantifier up.
       Return an expression with de-Bruijn indices and the list of names that were used.
       Return index of maximal variable.
    */

    unsigned pull_quantifier(bool is_forall, expr_ref& fml, ptr_vector<sort>* sorts, svector<symbol>* names);

};

#endif
