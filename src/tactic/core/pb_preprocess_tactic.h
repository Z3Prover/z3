/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_preprocess_tactic.h

Abstract:

    Pre-process pseudo-Boolean inequalities using 
    generalized Davis Putnam (resolution) to eliminate variables.

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-23

Notes:

--*/
#ifndef _PB_PREPROCESS_TACTIC_H_
#define _PB_PREPROCESS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_pb_preprocess_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("pb-preprocess", "pre-process pseudo-Boolean constraints a la Davis Putnam.", "mk_pb_preprocess_tactic(m, p)")
*/


#endif
