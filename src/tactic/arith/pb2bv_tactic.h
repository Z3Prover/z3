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
/*
  ADD_TACTIC("pb2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_pb2bv_tactic(m, p)")
*/

probe * mk_is_pb_probe();

/*
  ADD_PROBE("is-pb", "true if the goal is a pseudo-boolean problem.", "mk_is_pb_probe()")
*/

#endif
