/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qffpa_tactic.cpp

Abstract:

    Tactic for QF_FPA benchmarks.

Author:

    Christoph (cwinter) 2012-01-16

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"bit_blaster_tactic.h"
#include"sat_tactic.h"
#include"fpa2bv_tactic.h"

#include"qffpa_tactic.h"

tactic * mk_qffpa_tactic(ast_manager & m, params_ref const & p) {
    params_ref sat_simp_p = p;
    sat_simp_p .set_bool(":elim-and", true);

    return and_then(mk_simplify_tactic(m, p),
                    mk_fpa2bv_tactic(m, p),
                    using_params(mk_simplify_tactic(m, p), sat_simp_p),
                    mk_bit_blaster_tactic(m, p),
                    using_params(mk_simplify_tactic(m, p), sat_simp_p),
                    mk_sat_tactic(m, p),
                    mk_fail_if_undecided_tactic());
}
