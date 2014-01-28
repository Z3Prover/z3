/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffpa_tactic.h

Abstract:

    Tactic QF_FPA benchmarks.

Author:

    Christoph (cwinter) 2012-01-16

Notes:


--*/
#ifndef _QFFPA_TACTIC_H_
#define _QFFPA_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qffpa_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qffpa", "(try to) solve goal using the tactic for QF_FPA.", "mk_qffpa_tactic(m, p)")
  ADD_TACTIC("qffpabv", "(try to) solve goal using the tactic for QF_FPABV (floats+bit-vectors).", "mk_qffpa_tactic(m, p)")
*/

probe * mk_is_qffpa_probe();
probe * mk_is_qffpabv_probe();
/*
  ADD_PROBE("is-qffpa", "true if the goal is in QF_FPA (FloatingPoints).", "mk_is_qffpa_probe()")
  ADD_PROBE("is-qffpabv", "true if the goal is in QF_FPABV (FloatingPoints+Bitvectors).", "mk_is_qffpabv_probe()")
*/

#endif
