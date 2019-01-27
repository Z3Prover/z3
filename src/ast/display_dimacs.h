/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    display_dimacs.h

Abstract:

    Display expressions in DIMACS format.
    
Author:

    Nikolaj Bjorner (nbjorner0 2019-01-24

Revision History:

--*/
#ifndef DISPLAY_DIMACS_H_
#define DISPLAY_DIMACS_H_

#include "ast.h"

std::ostream& display_dimacs(std::ostream& out, expr_ref_vector const& fmls);

#endif /* DISPLAY_DIMACS_H__ */
