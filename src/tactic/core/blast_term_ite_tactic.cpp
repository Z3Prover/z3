/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    blast_term_ite_tactic.cpp

Abstract:

    Blast term if-then-else by hoisting them up.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-11-4

--*/
#include "tactic/core/blast_term_ite_tactic.h"

void blast_term_ite(expr_ref& fml, unsigned max_inflation) {
    blast_term_ite_simplifier::blast_term_ite(fml, max_inflation);
}

