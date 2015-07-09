/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nl_purify_tactic.h

Abstract:

    Tactic for purifying quantifier-free formulas that mix QF_NRA and other theories.
    It is designed to allow cooprating between the nlsat solver and other theories
    in a decoubled way.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-5.

Revision History:

--*/
#ifndef NL_PURIFY_TACTIC_H_
#define NL_PURIFY_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_nl_purify_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("nl-purify", "Decompose goal into pure NL-sat formula and formula over other theories.", "mk_nl_purify_tactic(m, p)")
*/

#endif

