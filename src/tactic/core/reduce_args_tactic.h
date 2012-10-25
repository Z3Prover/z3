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
/*
  ADD_TACTIC("reduce-args", "reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.", "mk_reduce_args_tactic(m, p)")
*/

#endif
