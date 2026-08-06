/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nl_linear_probe_tactic.h

Abstract:

    A short bounds-only probe for nonlinear arithmetic followed by the
    regular SMT tactic.

    The probe runs the SMT solver with every nonlinear lemma mechanism
    disabled (no Grobner, no Horner, no nlsat): only linear reasoning,
    linearization of monomials with fixed factors, and row-implied bound
    tightening act. On effectively-linear problems - monomials whose
    factors are pinned by fixed constants, as in bit-level arithmetic
    over power-of-two limbs - this decides the query at a fraction of
    the cost and with none of the seed variance of the lemma machinery;
    when bound reasoning cannot decide the query the probe fails fast
    and the unchanged default SMT tactic runs on a fresh solver.

Author:

    Lev Nachmanson (levnach) 2026-08-06

--*/
#pragma once

#include "util/params.h"

class ast_manager;
class tactic;

tactic * mk_nl_linear_probe_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("nl-linear-probe", "short bounds-only linear probe for nonlinear arithmetic, falling back to the smt tactic.", "mk_nl_linear_probe_tactic(m, p)")
*/
