/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    injectivity_tactic.h

Abstract:

    Injectivity tactics

Author:

    Nicolas Braud-Santoni (t-nibrau) 2017-08-10

Notes:

--*/
#ifndef INJECTIVITY_TACTIC_H_
#define INJECTIVITY_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_injectivity_tactic(ast_manager & m);

/*
  ADD_TACTIC("injectivity",  "Identifies and applies injectivity axioms.", "mk_injectivity_tactic(m)")
*/

#endif
