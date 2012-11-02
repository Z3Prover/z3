/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_strategic_solver.h

Abstract:

    Create a strategic solver with tactic for all main logics
    used in SMT.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"cmd_context.h"
#include"strategic_solver.h"
#include"qfbv_tactic.h"
#include"qflia_tactic.h"
#include"qfnia_tactic.h"
#include"qfnra_tactic.h"
#include"qfuf_tactic.h"
#include"qflra_tactic.h"
#include"quant_tactics.h"
#include"qfauflia_tactic.h"
#include"qfaufbv_tactic.h"
#include"qfufbv_tactic.h"
#include"qfidl_tactic.h"
#include"default_tactic.h"
#include"ufbv_tactic.h"
#include"qffpa_tactic.h"
#include"smt_solver.h"

MK_SIMPLE_TACTIC_FACTORY(qfuf_fct, mk_qfuf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfidl_fct, mk_qfidl_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfauflia_fct, mk_qfauflia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(auflia_fct, mk_auflia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(auflira_fct, mk_auflira_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(aufnira_fct, mk_aufnira_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(ufnia_fct, mk_ufnia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(uflra_fct, mk_uflra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(lra_fct, mk_lra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfbv_fct, mk_qfbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(default_fct, mk_default_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfaufbv_fct, mk_qfaufbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qflra_fct, mk_qflra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qflia_fct, mk_qflia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfufbv_fct, mk_qfufbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfnia_fct, mk_qfnia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfnra_fct, mk_qfnra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qffpa_fct, mk_qffpa_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(ufbv_fct, mk_ufbv_tactic(m, p));

static void init(strategic_solver * s) {
    s->set_default_tactic(alloc(default_fct));
    s->set_tactic_for(symbol("QF_UF"),     alloc(qfuf_fct));
    s->set_tactic_for(symbol("QF_BV"),     alloc(qfbv_fct));
    s->set_tactic_for(symbol("QF_IDL"),    alloc(qfidl_fct));
    s->set_tactic_for(symbol("QF_LIA"),    alloc(qflia_fct));
    s->set_tactic_for(symbol("QF_LRA"),    alloc(qflra_fct));
    s->set_tactic_for(symbol("QF_NIA"),    alloc(qfnia_fct));
    s->set_tactic_for(symbol("QF_NRA"),    alloc(qfnra_fct));
    s->set_tactic_for(symbol("QF_AUFLIA"), alloc(qfauflia_fct));
    s->set_tactic_for(symbol("QF_AUFBV"),  alloc(qfaufbv_fct));
    s->set_tactic_for(symbol("QF_ABV"),    alloc(qfaufbv_fct));
    s->set_tactic_for(symbol("QF_UFBV"),   alloc(qfufbv_fct));
    s->set_tactic_for(symbol("AUFLIA"),    alloc(auflia_fct));
    s->set_tactic_for(symbol("AUFLIRA"),   alloc(auflira_fct));
    s->set_tactic_for(symbol("AUFNIRA"),   alloc(aufnira_fct));
    s->set_tactic_for(symbol("UFNIA"),     alloc(ufnia_fct));
    s->set_tactic_for(symbol("UFLRA"),     alloc(uflra_fct));
    s->set_tactic_for(symbol("LRA"),       alloc(lra_fct));
    s->set_tactic_for(symbol("UFBV"),      alloc(ufbv_fct));
    s->set_tactic_for(symbol("BV"),        alloc(ufbv_fct));        
    s->set_tactic_for(symbol("QF_FPA"),    alloc(qffpa_fct));
}

solver * mk_smt_strategic_solver(bool force_tactic) {
    strategic_solver * s = alloc(strategic_solver);
    s->force_tactic(force_tactic);
    s->set_inc_solver(mk_smt_solver());
    init(s);
    return s;
}
