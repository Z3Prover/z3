/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    degree_shift_tactic.h

Abstract:

    Simple degree shift procedure. 
    Basic idea: if goal G contains a real variable x, x occurs with degrees
    d_1, ..., d_k in G, and n = gcd(d_1, ..., d_k) > 1. 
    Then, replace x^n with a new fresh variable y.

Author:

    Leonardo de Moura (leonardo) 2011-12-30.

Revision History:

--*/
#pragma once

#include "util/params.h"
class ast_manager;
class tactic;

tactic * mk_degree_shift_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("degree-shift", "try to reduce degree of polynomials (remark: :mul2power simplification is automatically applied).", "mk_degree_shift_tactic(m, p)")
*/

