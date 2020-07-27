/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    arith_bounds_tactic.h

Abstract:

    Fast/rudimentary arithmetic subsumption tactic.

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-6

Notes:

    Background: The Farkas learner in PDR generates tons 
    of inequalities that contain redundancies.
    It therefore needs a fast way to reduce these redundancies before
    passing the results to routines that are more expensive.
    The arith subsumption_strategy encapsulates a rudimentary 
    routine for simplifying inequalities. Additional simplification
    routines can be added here or composed with this strategy.

    Note: The bound_manager subsumes some of the collection methods used
    for assembling bounds, but it does not have a way to check for
    subsumption of atoms. 

--*/
#pragma once
#include "tactic/tactic.h"

tactic * mk_arith_bounds_tactic(ast_manager & m, params_ref const & p = params_ref());

