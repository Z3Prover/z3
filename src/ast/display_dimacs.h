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
#pragma once

#include "ast.h"

std::ostream& display_dimacs(std::ostream& out, expr_ref_vector const& fmls, bool include_names);

std::ostream& display_wcnf(std::ostream& out, expr_ref_vector const& fmls, svector<std::pair<expr*,unsigned>> const& soft);

