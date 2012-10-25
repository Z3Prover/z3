/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    occf_tactic.h

Abstract:

    Put clauses in the assertion set in
    OOC (one constraint per clause) form.
    Constraints occuring in formulas that
    are not clauses are ignored.
    The formula can be put into CNF by
    using mk_sat_preprocessor strategy.

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#ifndef _OCCF_TACTIC_H_
#define _OCCF_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_occf_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("occf", "put goal in one constraint per clause normal form (notes: fails if proof generation is enabled; only clauses are considered).", "mk_occf_tactic(m, p)")
*/

#endif

