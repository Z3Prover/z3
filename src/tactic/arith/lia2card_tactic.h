/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    lia2card_tactic.h

Abstract:

    Extract 0-1 integer variables used in 
    cardinality constraints and replace them by Booleans.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-5

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_lia2card_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("lia2card", "introduce cardinality constraints from 0-1 integer.", "mk_lia2card_tactic(m, p)")
*/

bool get_pb_sum(expr* term, expr_ref_vector& args, vector<rational>& coeffs, rational& coeff);

