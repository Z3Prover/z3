/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    default_tactic.h

Abstract:

    General purpose tactic for the Z3 logic (when the logic is not specified).

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#ifndef DEFAULT_TACTIC_H_
#define DEFAULT_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_default_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
ADD_TACTIC("default", "default strategy used when no logic is specified.", "mk_default_tactic(m, p)")
*/

#endif
