/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    blast_term_ite_tactic.h

Abstract:

    Blast term if-then-else by hoisting them up.
    This is expensive but useful in some cases, such as
    for enforcing constraints being in difference logic.
    Use elim-term-ite elsewhere when possible.
   

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-4

Notes:

--*/
#ifndef _BLAST_TERM_ITE_TACTIC_H_
#define _BLAST_TERM_ITE_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_blast_term_ite_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("blast-term-ite", "blast term if-then-else by hoisting them.", "mk_blast_term_ite_tactic(m, p)")
*/

void blast_term_ite(expr_ref& fml);

#endif
