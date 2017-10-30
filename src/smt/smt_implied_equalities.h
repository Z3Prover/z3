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


#ifndef SMT_IMPLIED_EQUALITIES_H_
#define SMT_IMPLIED_EQUALITIES_H_

#include "smt/smt_solver.h"
#include "util/lbool.h"
#include "ast/ast.h"


namespace smt {
        
    lbool implied_equalities(
        ast_manager & m, 
        solver & solver,
        unsigned num_terms, expr* const* terms, 
        unsigned* class_ids);            

    
};


#endif
