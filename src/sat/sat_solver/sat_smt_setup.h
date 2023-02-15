/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    sat_smt_setup.h

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-17

--*/
#pragma once

#include "ast/ast.h"
#include "smt/params/smt_params.h"
#include "sat/sat_config.h"
#include "ast/simplifiers/dependent_expr_state.h"

struct static_features;

namespace sat_smt {

    void setup_sat_config(smt_params const& p, sat::config& config);

    class setup {
        ast_manager&          m;
        dependent_expr_state& m_st;
        smt_params&           m_params;
        symbol                m_logic;
        bool                  m_already_configured = false;
        
        void setup_auto_config();
        void setup_default();
        //
        // setup_<logic>() methods do not depend on static features of the formula. So, they are safe to use
        // even in an incremental setting. 
        //
        // setup_<logic>(static_features & st) can only be used if the logical context will perform a single 
        // check.
        // 
        void setup_QF_DT();
        void setup_QF_UF();
        void setup_QF_UF(static_features const & st);
        void setup_QF_RDL();
        void setup_QF_RDL(static_features & st);
        void setup_QF_IDL();
        void setup_QF_IDL(static_features & st);
        void setup_QF_UFIDL();
        void setup_QF_UFIDL(static_features & st);
        void setup_QF_LRA();
        void setup_QF_LRA(static_features const & st);
        void setup_QF_LIA();
        void setup_QF_LIRA(static_features const& st);
        void setup_QF_LIA(static_features const & st);
        void setup_QF_UFLIA();
        void setup_QF_UFLIA(static_features & st);
        void setup_QF_UFLRA();
        void setup_QF_BV();
        void setup_QF_AUFBV();
        void setup_QF_AX();
        void setup_QF_AX(static_features const & st);
        void setup_QF_AUFLIA();
        void setup_QF_AUFLIA(static_features const & st);
        void setup_QF_FP();
        void setup_QF_FPBV();
        void setup_QF_S();
        void setup_LRA();
        void setup_CSP();
        void setup_AUFLIA(bool simple_array = true);
        void setup_AUFLIA(static_features const & st);
        void setup_AUFLIRA(bool simple_array = true);
        void setup_UFNIA();
        void setup_UFLRA();
        void setup_AUFLIAp();
        void setup_AUFNIRA();
        void setup_QF_BVRE();
        void setup_unknown();
        void setup_unknown(static_features & st);

    public:
        setup(ast_manager& m, dependent_expr_state& st, smt_params & params);
        void setk_already_configured() { m_already_configured = true; }
        bool already_configured() const { return m_already_configured; }
        symbol const & get_logic() const { return m_logic; }
        void operator()();        
    };
};


