/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_tactic.h

Abstract:

    smt::context as a tactic.

Author:

    Leonardo (leonardo) 2011-10-18

Notes:

--*/
#ifndef SMT_TACTIC_H_
#define SMT_TACTIC_H_

#include "util/params.h"
#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "tactic/goal.h"

class tactic;
class filter_model_converter;

tactic * mk_smt_tactic(ast_manager& m, params_ref const & p = params_ref(), symbol const& logic = symbol::null);
// syntax sugar for using_params(mk_smt_tactic(), p) where p = (:auto_config, auto_config)
tactic * mk_smt_tactic_using(ast_manager& m, bool auto_config = true, params_ref const & p = params_ref());

tactic * mk_parallel_smt_tactic(ast_manager& m, params_ref const& p);


/*
  ADD_TACTIC("smt", "apply a SAT based SMT solver.", "mk_smt_tactic(m, p)") 
  ADD_TACTIC("psmt", "builtin strategy for SMT tactic in parallel.", "mk_parallel_smt_tactic(m, p)")
*/
#endif
