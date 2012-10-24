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
#ifndef _BV1_BLASTER_TACTIC_H_
#define _BV1_BLASTER_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_bv1_blaster_tactic(ast_manager & m, params_ref const & p = params_ref());
probe * mk_is_qfbv_eq_probe();

#endif
