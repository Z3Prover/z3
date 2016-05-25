/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nra_tactic.h

Abstract:

    Tactic for NRA

Author:

    Leonardo (leonardo) 2012-03-13

Notes:

--*/
#ifndef NRA_TACTIC_H_
#define NRA_TACTIC_H_

tactic * mk_nra_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
ADD_TACTIC("nra", "builtin strategy for solving NRA problems.", "mk_nra_tactic(m, p)")
*/

#endif
