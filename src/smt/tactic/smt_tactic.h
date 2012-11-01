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
#ifndef _SMT_TACTIC_H_
#define _SMT_TACTIC_H_

#include"params.h"

class tactic;

tactic * mk_smt_tactic(params_ref const & p = params_ref());
// syntax sugar for using_params(mk_smt_tactic(), p) where p = (:auto_config, auto_config)
tactic * mk_smt_tactic_using(bool auto_config = true, params_ref const & p = params_ref());

/*
  ADD_TACTIC("smt", "apply a SAT based SMT solver.", "mk_smt_tactic(p)") 
*/

#endif
