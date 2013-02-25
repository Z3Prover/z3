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
#ifndef _QUANT_TACTICS_H_
#define _QUANT_TACTICS_H_

#include"params.h"
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

#endif
