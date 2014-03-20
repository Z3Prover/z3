/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

Notes:

--*/
#ifndef _CARD2BV_TACTIC_
#define _CARD2BV_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_card2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_card2bv_tactic(m, p)")
*/


#endif
