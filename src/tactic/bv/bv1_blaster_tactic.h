/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster_tactic.h

Abstract:

    Rewriter for "blasting" bit-vectors of size n into bit-vectors of size 1.
    This rewriter only supports concat and extract operators.
    This transformation is useful for handling benchmarks that contain
    many BV equalities. 

    Remark: other operators can be mapped into concat/extract by using
    the simplifiers.

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#ifndef BV1_BLASTER_TACTIC_H_
#define BV1_BLASTER_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_bv1_blaster_tactic(ast_manager & m, params_ref const & p = params_ref());
probe * mk_is_qfbv_eq_probe();
/*
  ADD_TACTIC("bv1-blast", "reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).", "mk_bv1_blaster_tactic(m, p)")
  ADD_PROBE("is-qfbv-eq", "true if the goal is in a fragment of QF_BV which uses only =, extract, concat.", "mk_is_qfbv_eq_probe()")
*/
#endif
