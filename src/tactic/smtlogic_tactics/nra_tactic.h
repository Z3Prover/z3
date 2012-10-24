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
#ifndef _NRA_TACTIC_H_
#define _NRA_TACTIC_H_

tactic * mk_nra_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
