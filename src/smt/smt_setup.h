/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_setup.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-24.

Revision History:

--*/
#ifndef _SMT_SETUP_H_
#define _SMT_SETUP_H_

#include"ast.h"
#include"smt_params.h"

struct static_features;
namespace smt {
    
    enum config_mode {
        CFG_BASIC,   // install theories based on user options
        CFG_LOGIC,   // install theories and configure Z3 based on the value of the parameter set-logic.
        CFG_AUTO,    // install theories based on static features of the input formula
    };

    class context;
    /**
       \brief Object used to setup a logical context.
       
       \warning In the current version, we can only setup a logical context at scope level 0,
       and before internalizing any formula. Auxiliary temporary contexts are used to avoid this
       limitation.
    */
    class setup {
        context &          m_context;
        ast_manager &      m_manager;
        smt_params &       m_params;
        symbol             m_logic;
        bool               m_already_configured;
        void setup_auto_config();
        void setup_default();
        //
        // setup_<logic>() methods do not depend on static features of the formula. So, they are safe to use
        // even in an incremental setting. 
        //
        // setup_<logic>(static_features & st) can only be used if the logical context will perform a single 
        // check.
        // 
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
        void setup_LRA();
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
        void setup_arrays();
        void setup_datatypes();
        void setup_bv();
        void setup_arith();
        void setup_dl();
        void setup_seq();
        void setup_card();
        void setup_i_arith();
        void setup_mi_arith();
        void setup_fpa();

    public:
        setup(context & c, smt_params & params);
        void mark_already_configured() { m_already_configured = true; }
        bool already_configured() const { return m_already_configured; }
        bool set_logic(symbol logic) { 
            if (already_configured()) 
                return false;
            m_logic = logic; 
            return true;
        }
        symbol const & get_logic() const { return m_logic; }
        void operator()(config_mode cm);
    };
};

#endif /* _SMT_SETUP_H_ */

