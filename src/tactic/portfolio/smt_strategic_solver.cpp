/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_strategic_solver.cpp

Abstract:

    Create a strategic solver with tactic for all main logics
    used in SMT.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include "cmd_context/cmd_context.h"
#include "solver/combined_solver.h"
#include "solver/tactic2solver.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/qflia_tactic.h"
#include "tactic/smtlogics/qfnia_tactic.h"
#include "tactic/smtlogics/qfnra_tactic.h"
#include "tactic/smtlogics/qfuf_tactic.h"
#include "tactic/smtlogics/qflra_tactic.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/smtlogics/qfauflia_tactic.h"
#include "tactic/smtlogics/qfaufbv_tactic.h"
#include "tactic/smtlogics/qfufbv_tactic.h"
#include "tactic/smtlogics/qfidl_tactic.h"
#include "tactic/smtlogics/nra_tactic.h"
#include "tactic/portfolio/default_tactic.h"
#include "tactic/fd_solver/fd_solver.h"
#include "tactic/fd_solver/smtfd_solver.h"
#include "tactic/ufbv/ufbv_tactic.h"
#include "tactic/fpa/qffp_tactic.h"
#include "muz/fp/horn_tactic.h"
#include "smt/smt_solver.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "ast/rewriter/bv_rewriter.h"
#include "solver/solver2tactic.h"
#include "solver/parallel_tactic.h"
#include "solver/parallel_params.hpp"
#include "tactic/tactic_params.hpp"
#include "parsers/smt2/smt2parser.h"



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
    else if (logic=="NRA")
        return mk_nra_tactic(m, p);
    else if (logic=="LIA")
        return mk_lia_tactic(m, p);
    else if (logic=="UFBV")
        return mk_ufbv_tactic(m, p);
    else if (logic=="BV")
        return mk_ufbv_tactic(m, p);
    else if (logic=="QF_FP")
        return mk_qffp_tactic(m, p);
    else if (logic == "QF_FPBV" || logic == "QF_BVFP")
        return mk_qffpbv_tactic(m, p);
    else if (logic=="HORN")
        return mk_horn_tactic(m, p);
    else if ((logic == "QF_FD" || logic == "SAT") && !m.proofs_enabled())
        return mk_fd_tactic(m, p);
    else 
        return mk_default_tactic(m, p);
}

static solver* mk_special_solver_for_logic(ast_manager & m, params_ref const & p, symbol const& logic) {
    parallel_params pp(p);
    if ((logic == "QF_FD" || logic == "SAT") && !m.proofs_enabled() && !pp.enable())
        return mk_fd_solver(m, p);
    if (logic == "SMTFD" && !m.proofs_enabled() && !pp.enable())
        return mk_smtfd_solver(m, p);
    return nullptr;
}

static solver* mk_solver_for_logic(ast_manager & m, params_ref const & p, symbol const& logic) {
    bv_rewriter rw(m);
    solver* s = mk_special_solver_for_logic(m, p, logic);
    tactic_params tp;
    if (!s && logic == "QF_BV" && rw.hi_div0()) 
        s = mk_inc_sat_solver(m, p);
    if (!s && tp.default_tactic() == "sat")
        s = mk_inc_sat_solver(m, p);
    if (!s) 
        s = mk_smt_solver(m, p, logic);
    return s;
}

class smt_strategic_solver_factory : public solver_factory {
    symbol m_logic;
public:
    smt_strategic_solver_factory(symbol const & logic):m_logic(logic) {}
    
    ~smt_strategic_solver_factory() override {}
    solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) override {
        symbol l;
        if (m_logic != symbol::null)
            l = m_logic;
        else
            l = logic;

        tactic_params tp;
        tactic_ref t;
        if (tp.default_tactic() != symbol::null &&
            !tp.default_tactic().is_numerical() && 
            tp.default_tactic().bare_str() && 
            tp.default_tactic().bare_str()[0]) {
            cmd_context ctx(false, &m, l);
            std::istringstream is(tp.default_tactic().bare_str());
            char const* file_name = "";
            sexpr_ref se = parse_sexpr(ctx, is, p, file_name);
            if (se) {
                t = sexpr2tactic(ctx, se.get());
            }
        }

        if (!t) {
            solver* s = mk_special_solver_for_logic(m, p, l);
            if (s) return s;
        }
        if (!t) {
            t = mk_tactic_for_logic(m, p, l);
        }
        return mk_combined_solver(mk_tactic2solver(m, t.get(), p, proofs_enabled, models_enabled, unsat_core_enabled, l),
                                  mk_solver_for_logic(m, p, l), 
                                  p);
    }
};

solver_factory * mk_smt_strategic_solver_factory(symbol const & logic) {
    return alloc(smt_strategic_solver_factory, logic);
}

solver* mk_smt2_solver(ast_manager& m, params_ref const& p) {
    return mk_inc_sat_solver(m, p);
}
