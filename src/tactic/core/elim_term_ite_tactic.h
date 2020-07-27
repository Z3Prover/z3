/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_term_ite_tactic.h

Abstract:

    Eliminate term if-then-else by adding 
    new fresh auxiliary variables.

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_elim_term_ite_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("elim-term-ite", "eliminate term if-then-else by adding fresh auxiliary declarations.", "mk_elim_term_ite_tactic(m, p)")
*/

