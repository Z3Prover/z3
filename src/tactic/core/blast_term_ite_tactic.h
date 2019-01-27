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
#ifndef BLAST_TERM_ITE_TACTIC_H_
#define BLAST_TERM_ITE_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_blast_term_ite_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
    ADD_TACTIC("blast-term-ite", "blast term if-then-else by hoisting them.", "mk_blast_term_ite_tactic(m, p)")
*/

void blast_term_ite(expr_ref& fml, unsigned max_inflation);

#endif
