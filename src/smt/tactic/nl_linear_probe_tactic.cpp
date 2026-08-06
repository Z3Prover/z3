/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nl_linear_probe_tactic.cpp

Abstract:

    See nl_linear_probe_tactic.h.

Author:

    Lev Nachmanson (levnach) 2026-08-06

--*/
#include "smt/tactic/nl_linear_probe_tactic.h"
#include "smt/tactic/smt_tactic_core.h"
#include "tactic/tactical.h"

tactic * mk_nl_linear_probe_tactic(ast_manager & m, params_ref const & p) {
    // The probe: solver 6 restricted to its linear machinery. Grobner,
    // Horner and nlsat are off; row-implied bound propagation is allowed to
    // improve existing bounds, which drives the factor-bounds -> product
    // bounds -> farkas cascade to completion on effectively-linear queries.
    params_ref probe_p = p;
    probe_p.set_uint("arith.solver", 6);
    probe_p.set_bool("arith.nl.grobner", false);
    probe_p.set_bool("arith.nl.horner", false);
    probe_p.set_bool("arith.nl.nra", false);
    probe_p.set_bool("arith.nl.nra_check_assignment", false);
    probe_p.set_bool("arith.nl.propagate_row_bounds_improve", true);

    unsigned timeout_ms = p.get_uint("probe_timeout", 300);

    return or_else(try_for(using_params(mk_smt_tactic_core(m), probe_p), timeout_ms),
                   mk_smt_tactic_core(m, p));
}
