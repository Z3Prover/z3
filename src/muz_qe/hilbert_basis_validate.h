/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hilbert_basis_validate.h

Abstract:

    Basic Hilbert Basis validation.

    hilbert_basis computes a Hilbert basis for linear
    homogeneous inequalities over naturals.

Author:

    Nikolaj Bjorner (nbjorner) 2013-02-15.

Revision History:

--*/

#ifndef _HILBERT_BASIS_VALIDATE_H_
#define _HILBERT_BASIS_VALIDATE_H_

#include "hilbert_basis.h"
#include "ast.h"

class hilbert_basis_validate {
    ast_manager& m;

    void validate_solution(hilbert_basis& hb, vector<rational> const& v, bool is_initial);

public:
        
    hilbert_basis_validate(ast_manager& m);

    expr_ref mk_validate(hilbert_basis& hb);

};


#endif 
