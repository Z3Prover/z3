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
#include"combined_solver.h"
#include"tactic2solver.h"
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
#include"qffp_tactic.h"
#include"horn_tactic.h"
#include"smt_solver.h"

tactic * mk_tactic_for_logic(ast_manager & m, params_ref const & p, symbol const & logic) {
    if (logic=="QF_UF")
        return mk_qfuf_tactic(m, p);
    else if (logic=="QF_BV")
        return mk_qfbv_tactic(m, p);        
    else if (logic=="QF_IDL")
        return mk_qfidl_tactic(m, p);
    else if (logic=="QF_LIA")
        return mk_qflia_tactic(m, p);
    else if (logic=="QF_LRA")
        return mk_qflra_tactic(m, p);
    else if (logic=="QF_NIA")
        return mk_qfnia_tactic(m, p);
    else if (logic=="QF_NRA")
        return mk_qfnra_tactic(m, p);
    else if (logic=="QF_AUFLIA")
        return mk_qfauflia_tactic(m, p);
    else if (logic=="QF_AUFBV")
        return mk_qfaufbv_tactic(m, p);
    else if (logic=="QF_ABV")
        return mk_qfaufbv_tactic(m, p);
    else if (logic=="QF_UFBV")
        return mk_qfufbv_tactic(m, p);
    else if (logic=="AUFLIA")
        return mk_auflia_tactic(m, p);
    else if (logic=="AUFLIRA")
        return mk_auflira_tactic(m, p);
    else if (logic=="AUFNIRA")
        return mk_aufnira_tactic(m, p);
    else if (logic=="UFNIA")
        return mk_ufnia_tactic(m, p);
    else if (logic=="UFLRA")
        return mk_uflra_tactic(m, p);
    else if (logic=="LRA")
        return mk_lra_tactic(m, p);
    else if (logic=="LIA")
        return mk_lia_tactic(m, p);
    else if (logic=="UFBV")
        return mk_ufbv_tactic(m, p);
    else if (logic=="BV")
        return mk_ufbv_tactic(m, p);
    else if (logic=="QF_FP")
        return mk_qffp_tactic(m, p);
    else if (logic == "QF_FPBV")
        return mk_qffpbv_tactic(m, p);
    else if (logic=="HORN")
        return mk_horn_tactic(m, p);
    else 
        return mk_default_tactic(m, p);
}

class smt_strategic_solver_factory : public solver_factory {
    symbol m_logic;
public:
    smt_strategic_solver_factory(symbol const & logic):m_logic(logic) {}
    
    virtual ~smt_strategic_solver_factory() {}
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        symbol l;
        if (m_logic != symbol::null)
            l = m_logic;
        else
            l = logic;
        tactic * t = mk_tactic_for_logic(m, p, l);
        return mk_combined_solver(mk_tactic2solver(m, t, p, proofs_enabled, models_enabled, unsat_core_enabled, l),
                                  mk_smt_solver(m, p, l),
                                  p);
    }
};

solver_factory * mk_smt_strategic_solver_factory(symbol const & logic) {
    return alloc(smt_strategic_solver_factory, logic);
}

