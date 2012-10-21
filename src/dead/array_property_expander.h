/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    array_property_expander.h

Abstract:

    Expand array operations for the array property fragment formulas.

Author:

    Nikolaj Bjorner (nbjorner) 2010-16-12

Revision History:

--*/
#ifndef _ARRAY_PROPERTY_EXPANDER_H_
#define _ARRAY_PROPERTY_EXPANDER_H_

#include"ast.h"

class array_property_expander {
    ast_manager& m_manager;
public:
    array_property_expander(ast_manager& m);
    void operator()(unsigned num_fmls, expr* const* fmls, expr_ref_vector& result);    
};


#endif /* _ARRAY_PROPERTY_EXPANDER_H_ */

