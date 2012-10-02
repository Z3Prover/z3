/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    interpolant_provider.h

Abstract:

    Interface for obtaining interpolants.

Author:

    Krystof Hoder (t-khoder) 2011-10-19.

Revision History:

--*/

#include "ast.h"
#include "lbool.h"
#include "model.h"
#include "params.h"

#ifndef _PDR_INTERPOLANT_PROVIDER_H_
#define _PDR_INTERPOLANT_PROVIDER_H_

class interpolant_provider
{
protected:
    ast_manager & m;

    interpolant_provider(ast_manager& m) : m(m) {}

public:

    virtual ~interpolant_provider() {}

    /**
    If (f1 /\ f2) is unsatisfiable, return true and into res assign a formula
    I such that f1 --> I, I --> ~f2, and the language if I is in the intersection 
    of languages of f1 and f2.

    If (f1 /\ f2) is satisfiable, return false.
    */
    virtual lbool get_interpolant(expr * f1, expr * f2, expr_ref& res) = 0;

    static interpolant_provider * mk(ast_manager& m, params_ref const& p);

    static void output_interpolant(ast_manager& m, expr* A, expr* B, expr* I);
};


#endif
