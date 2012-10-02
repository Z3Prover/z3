/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    array_property_recognizer.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-16-12

Revision History:

--*/
#ifndef _ARRAY_PROPERTY_RECOGNIZER_H_
#define _ARRAY_PROPERTY_RECOGNIZER_H_

#include"ast.h"

class array_property_recognizer {
    ast_manager& m_manager;
public:
    array_property_recognizer(ast_manager& m);
    bool operator()(unsigned num_fmls, expr* const* fmls);    
};


#endif /* _ARRAY_PROPERTY_RECOGNIZER_H_ */

