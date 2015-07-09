/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    macro_finder_tactic.h

Abstract:

    Macro finder

Author:

    Christoph (cwinter) 2012-10-26

Notes:

--*/
#ifndef MACRO_FINDER_TACTIC_H_
#define MACRO_FINDER_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_macro_finder_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("macro-finder",  "Identifies and applies macros.", "mk_macro_finder_tactic(m, p)")
*/

#endif
