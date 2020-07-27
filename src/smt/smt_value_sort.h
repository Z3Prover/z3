/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_value_sort.h

Abstract:

    Determine if elements of a given sort can be values.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-25

Revision History:


--*/


#pragma once

#include "ast/ast.h"


namespace smt {
        
    bool is_value_sort(ast_manager& m, sort* s);

    bool is_value_sort(ast_manager& m, expr* e);
    
};


