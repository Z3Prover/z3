/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    reduce_args_tactic.h

Abstract:

    Reduce the number of arguments in function applications.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef _REDUCE_ARGS_TACTIC_H_
#define _REDUCE_ARGS_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_reduce_args_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
