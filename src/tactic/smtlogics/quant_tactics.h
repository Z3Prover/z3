/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quant_tactics.h

Abstract:

    Tactics for benchmarks containing quantifiers.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-21.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_ufnia_tactic(ast_manager & m, params_ref const & p);
tactic * mk_uflra_tactic(ast_manager & m, params_ref const & p);
tactic * mk_auflia_tactic(ast_manager & m, params_ref const & p);
tactic * mk_auflira_tactic(ast_manager & m, params_ref const & p);
tactic * mk_aufnira_tactic(ast_manager & m, params_ref const & p);
tactic * mk_lra_tactic(ast_manager & m, params_ref const & p);
tactic * mk_lia_tactic(ast_manager & m, params_ref const & p);
tactic * mk_lira_tactic(ast_manager & m, params_ref const & p);

/*
  ADD_TACTIC("ufnia", "builtin strategy for solving UFNIA problems.", "mk_ufnia_tactic(m, p)")
  ADD_TACTIC("uflra", "builtin strategy for solving UFLRA problems.", "mk_uflra_tactic(m, p)")
  ADD_TACTIC("auflia", "builtin strategy for solving AUFLIA problems.", "mk_auflia_tactic(m, p)")
  ADD_TACTIC("auflira", "builtin strategy for solving AUFLIRA problems.", "mk_auflira_tactic(m, p)")
  ADD_TACTIC("aufnira", "builtin strategy for solving AUFNIRA problems.", "mk_aufnira_tactic(m, p)")
  ADD_TACTIC("lra", "builtin strategy for solving LRA problems.", "mk_lra_tactic(m, p)")
  ADD_TACTIC("lia", "builtin strategy for solving LIA problems.", "mk_lia_tactic(m, p)")
  ADD_TACTIC("lira", "builtin strategy for solving LIRA problems.", "mk_lira_tactic(m, p)")

*/


