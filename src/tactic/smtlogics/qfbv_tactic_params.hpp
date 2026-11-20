/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    qfbv_tactic_params.hpp

Abstract:

    Keys of the 'tactic' module for the scopes of the QF_BV tactic
    (see scope_tactic in tactic/tactical.h).

    A key qfbv.<path>.<key> sets <key> for the step named qfbv.<path>; <path>.enabled
    false skips the step. The defaults are the values the QF_BV tactic sets as
    defaults (set_default_*), taken from qfbv_tactic_defaults below; a value the user
    sets replaces them.

--*/
#pragma once

#include "util/params.h"
#include "util/gparams.h"

#define QFBV_TACTIC_PARAMS_LIST(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(preamble_solve_eqs_enabled,  "qfbv.preamble.solve_eqs.enabled",  true,  "run solve-eqs in the QF_BV preamble (smt.solve_eqs=false disables it in any case)") \
  /* reaches solve-eqs as solve_eqs.max_occs through the scope qfbv.preamble, not the step scope */ \
  UINT_(preamble_solve_eqs_max_occs, "qfbv.preamble.solve_eqs.max_occs", 2,     "solve_eqs.max_occs in the QF_BV preamble: maximum number of occurrences for considering a variable for gaussian eliminations") \
  BOOL_(preamble_simp2_enabled,      "qfbv.preamble.simp2.enabled",      true,  "run the second simplify pass of the QF_BV preamble") \
  BOOL_(preamble_simp2_som,          "qfbv.preamble.simp2.som",          true,  "som in the second simplify pass of the QF_BV preamble (needs flat)") \
  BOOL_(preamble_simp2_flat,         "qfbv.preamble.simp2.flat",         true,  "flat in the second simplify pass of the QF_BV preamble") \
  BOOL_(preamble_simp2_hoist_mul,    "qfbv.preamble.simp2.hoist_mul",    false, "hoist_mul in the second simplify pass of the QF_BV preamble (off while som is on)") \
  BOOL_(preamble_simp2_push_ite_bv,  "qfbv.preamble.simp2.push_ite_bv",  false, "push_ite_bv in the second simplify pass of the QF_BV preamble") \
  BOOL_(preamble_hoist_enabled,      "qfbv.preamble.hoist.enabled",      true,  "run the hoist_mul simplify pass of the QF_BV preamble") \
  BOOL_(preamble_hoist_hoist_mul,    "qfbv.preamble.hoist.hoist_mul",    true,  "hoist_mul in the hoist simplify pass of the QF_BV preamble") \
  BOOL_(preamble_hoist_som,          "qfbv.preamble.hoist.som",          false, "som in the hoist simplify pass of the QF_BV preamble")

// No description: tactic_params.hpp registers the description of the "tactic" module.
Z3_DEFINE_MODULE_PARAMS(qfbv_tactic_params, "tactic", QFBV_TACTIC_PARAMS_LIST, nullptr);

// The defaults of the rows as constants, for the factory: it sets them with set_default_*
// and must not read user values, which reach the steps through updt_params.
#define QFBV_TACTIC_DEFAULT_UINT(method, key, deflt, doc) static constexpr unsigned method = deflt;
#define QFBV_TACTIC_DEFAULT_BOOL(method, key, deflt, doc) static constexpr bool method = deflt;
#define QFBV_TACTIC_DEFAULT_NONE(method, key, deflt, doc)
struct qfbv_tactic_defaults {
    QFBV_TACTIC_PARAMS_LIST(QFBV_TACTIC_DEFAULT_UINT, QFBV_TACTIC_DEFAULT_BOOL, QFBV_TACTIC_DEFAULT_NONE,
                            QFBV_TACTIC_DEFAULT_NONE, QFBV_TACTIC_DEFAULT_NONE)
};
#undef QFBV_TACTIC_DEFAULT_UINT
#undef QFBV_TACTIC_DEFAULT_BOOL
#undef QFBV_TACTIC_DEFAULT_NONE

#undef QFBV_TACTIC_PARAMS_LIST
