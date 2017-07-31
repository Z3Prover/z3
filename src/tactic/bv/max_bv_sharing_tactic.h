/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    max_bv_sharing_tactic.h

Abstract:

    Rewriter for "maximing" the number of shared terms.
    The idea is to rewrite AC terms to maximize sharing.
    This rewriter is particularly useful for reducing
    the number of Adders and Multipliers before "bit-blasting".

Author:

    Leonardo de Moura (leonardo) 2011-12-29.

Revision History:

--*/
#ifndef MAX_BV_SHARING_TACTIC_H_
#define MAX_BV_SHARING_TACTIC_H_

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_max_bv_sharing_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("max-bv-sharing", "use heuristics to maximize the sharing of bit-vector expressions such as adders and multipliers.", "mk_max_bv_sharing_tactic(m, p)")
*/

#endif

