/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    pb2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Christoph (cwinter) 2012-02-15

Notes:

--*/
#ifndef _PB2BV_TACTIC_
#define _PB2BV_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_pb2bv_tactic(ast_manager & m, params_ref const & p = params_ref());

probe * mk_is_pb_probe();

#endif
