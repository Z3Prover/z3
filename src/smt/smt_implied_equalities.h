/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_implied_equalities.h

Abstract:

    Procedure for obtaining implied equalities relative to the
    state of a solver.

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-29

Revision History:


--*/


#ifndef __SMT_IMPLIED_EQUALITIES_H__
#define __SMT_IMPLIED_EQUALITIES_H__

#include"smt_kernel.h"


namespace smt {
        
    lbool implied_equalities(
        kernel & solver,
        unsigned num_terms, expr* const* terms, 
        unsigned* class_ids);            

    
};


#endif
