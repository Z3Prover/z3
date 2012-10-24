/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_tactic.h

Abstract:

    General purpose tactic for UFBV benchmarks.

Author:

    Christoph (cwinter) 2012-10-24

Notes:

--*/
#ifndef _UFBV_TACTIC_H_
#define _UFBV_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_macro_finder_tactic(ast_manager & m, params_ref const & p);

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p);

#endif
