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
    tactic* simplify = mk_simplify_tactic(m, p);

    tactic* preamble = mk_preamble_tactic(m);
    tactic* lazy_smt = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_smt_tactic(m_ref, p_ref); });
    tactic* branch = and_then(preamble, lazy_smt);

    tactic* lazy_qffplra = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qffplra_tactic(m_ref, p_ref); });
    probe* qffplra_probe = mk_is_qffplra_probe();
    branch = cond(qffplra_probe, lazy_qffplra, branch);

    tactic* lazy_qffp = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qffp_tactic(m_ref, p_ref); });
    probe* qffp_probe = mk_is_qffp_probe();
    branch = cond(qffp_probe, lazy_qffp, branch);

    tactic* lazy_nra = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_nra_tactic(m_ref, p_ref); });
    probe* nra_probe = mk_is_nra_probe();
    branch = cond(nra_probe, lazy_nra, branch);

    tactic* lazy_lira = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_lira_tactic(m_ref, p_ref); });
    probe* lira_probe = mk_is_lira_probe();
    branch = cond(lira_probe, lazy_lira, branch);

    tactic* lazy_qfnia = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qfnia_tactic(m_ref, p_ref); });
    probe* qfnia_probe = mk_is_qfnia_probe();
    branch = cond(qfnia_probe, lazy_qfnia, branch);

    tactic* lazy_qfnra = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qfnra_tactic(m_ref, p_ref); });
    probe* qfnra_probe = mk_is_qfnra_probe();
    branch = cond(qfnra_probe, lazy_qfnra, branch);

    tactic* lazy_qflra = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qflra_tactic(m_ref, p_ref); });
    probe* qflra_probe = mk_is_qflra_probe();
    branch = cond(qflra_probe, lazy_qflra, branch);

    tactic* lazy_qfauflia = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qfauflia_tactic(m_ref, p_ref); });
    probe* qfauflia_probe = mk_is_qfauflia_probe();
    branch = cond(qfauflia_probe, lazy_qfauflia, branch);

    tactic* lazy_qflia = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qflia_tactic(m_ref, p_ref); });
    probe* qflia_probe = mk_is_qflia_probe();
    branch = cond(qflia_probe, lazy_qflia, branch);

    tactic* lazy_qfaufbv = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qfaufbv_tactic(m_ref, p_ref); });
    probe* qfaufbv_probe = mk_is_qfaufbv_probe();
    branch = cond(qfaufbv_probe, lazy_qfaufbv, branch);

    tactic* lazy_qfbv = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_qfbv_tactic(m_ref, p_ref); });
    probe* qfbv_probe = mk_is_qfbv_probe();
    branch = cond(qfbv_probe, lazy_qfbv, branch);

    tactic* lazy_fd = mk_lazy_tactic(m, p, [&](auto& m_ref, auto const& p_ref) { return mk_fd_tactic(m_ref, p_ref); });
    probe* propositional_probe = mk_is_propositional_probe();
    probe* produce_proofs_probe = mk_produce_proofs_probe();
    probe* no_proofs_probe = mk_not(produce_proofs_probe);
    probe* propositional_no_proofs = mk_and(propositional_probe, no_proofs_probe);
    branch = cond(propositional_no_proofs, lazy_fd, branch);

    tactic* combined = and_then(simplify, branch);
    tactic * st = using_params(combined, p);
    return st;
}
