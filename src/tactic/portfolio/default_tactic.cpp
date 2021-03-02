/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    default_tactic.cpp

Abstract:

    General purpose tactic for the Z3 logic (when the logic is not specified).

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#include "tactic/portfolio/default_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/qflia_tactic.h"
#include "tactic/smtlogics/qflra_tactic.h"
#include "tactic/smtlogics/qfnia_tactic.h"
#include "tactic/smtlogics/qfnra_tactic.h"
#include "tactic/smtlogics/nra_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/fpa/qffp_tactic.h"
#include "tactic/fpa/qffplra_tactic.h"
#include "tactic/smtlogics/qfaufbv_tactic.h"
#include "tactic/smtlogics/qfauflia_tactic.h"
#include "tactic/fd_solver/fd_solver.h"
#include "tactic/smtlogics/smt_tactic.h"

tactic * mk_default_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = using_params(and_then(mk_simplify_tactic(m),
                                        cond(mk_and(mk_is_propositional_probe(), mk_not(mk_produce_proofs_probe())), mk_fd_tactic(m, p),
                                        cond(mk_is_qfbv_probe(), mk_qfbv_tactic(m),
                                        cond(mk_is_qfaufbv_probe(), mk_qfaufbv_tactic(m),
                                        cond(mk_is_qflia_probe(), mk_qflia_tactic(m),
                                        cond(mk_is_qfauflia_probe(), mk_qfauflia_tactic(m),
                                        cond(mk_is_qflra_probe(), mk_qflra_tactic(m),
                                        cond(mk_is_qfnra_probe(), mk_qfnra_tactic(m),
                                        cond(mk_is_qfnia_probe(), mk_qfnia_tactic(m),
                                        cond(mk_is_lira_probe(), mk_lira_tactic(m, p),
                                        cond(mk_is_nra_probe(), mk_nra_tactic(m),
                                        cond(mk_is_qffp_probe(), mk_qffp_tactic(m, p),
                                        cond(mk_is_qffplra_probe(), mk_qffplra_tactic(m, p),
                                        //cond(mk_is_qfufnra_probe(), mk_qfufnra_tactic(m, p),
                                             and_then(mk_preamble_tactic(m), mk_smt_tactic(m))))))))))))))),
                               p);
    return st;
}

