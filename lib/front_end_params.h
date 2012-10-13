/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    front_end_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-05-10.

Revision History:

--*/
#ifndef _FRONT_END_PARAMS_H_
#define _FRONT_END_PARAMS_H_

#include"ini_file.h"
#include"ast.h"
#include"preprocessor_params.h"
#include"spc_params.h"
#include"smt_params.h"
#include"pp_params.h"
#include"parser_params.h"
#include"arith_simplifier_params.h"
#include"z3_solver_params.h"
#include"model_params.h"

enum engine {
    ENG_SMT,
    ENG_SPC,
    ENG_EPR
};

struct front_end_params : public preprocessor_params, public spc_params, public smt_params, public parser_params, 
                          public arith_simplifier_params, public z3_solver_params, public model_params
                           {
    ref<param_vector>   m_param_vector;
    engine              m_engine;
    unsigned            m_max_num_cex; // maximum number of counterexamples
    bool                m_at_labels_cex; // only use labels which contains the @ symbol when building multiple counterexamples.
    bool                m_check_at_labels; // check that @ labels are inserted to generate unique counter-examples.
    bool                m_default_qid;
    bool                m_interactive;
    bool                m_well_sorted_check;
    bool                m_ignore_bad_patterns;
    bool                m_ignore_user_patterns;
    bool                m_incremental_core_assert; // assert conditions to the core incrementally
    unsigned            m_soft_timeout;
    double              m_instr_out;
    unsigned            m_memory_high_watermark;
    unsigned            m_memory_max_size;
    proof_gen_mode      m_proof_mode;
    bool                m_auto_config;
    bool                m_smtlib2_compliant;
#ifdef Z3DEBUG
    int                 m_copy_params; // used for testing copy params... Invoke method copy_params(m_copy_params) in main.cpp when diff -1.
#endif
    bool                m_preprocess;  // temporary hack for disabling all preprocessing..
    bool                m_ignore_checksat; // abort before checksat... for internal debugging
    bool                m_debug_ref_count;
    bool                m_trace;
    std::string         m_trace_file_name;
    std::fstream*       m_trace_stream;
    bool                m_ignore_setparameter;
    bool                m_async_commands;
    bool                m_display_config;
    bool                m_user_theory_preprocess_axioms;
    bool                m_user_theory_persist_axioms;
    bool                m_nlsat; // temporary hack until strategic_solver is ported to new tactic framework

    front_end_params():
        m_param_vector(alloc(param_vector, this)),
        m_engine(ENG_SMT),
        m_max_num_cex(1),
        m_at_labels_cex(false),
        m_check_at_labels(false),
        m_default_qid(false),
        m_interactive(false),
        m_well_sorted_check(true),
        m_ignore_bad_patterns(true),
        m_ignore_user_patterns(false),
        m_incremental_core_assert(true),
        m_soft_timeout(0),
        m_instr_out(0.0),
        m_memory_high_watermark(0),
        m_memory_max_size(0),
        m_proof_mode(PGM_DISABLED),
#if    defined(SMTCOMP) || defined(_EXTERNAL_RELEASE)
        m_auto_config(true),
#else
        m_auto_config(false), 
#endif
#if    0 
        m_smtlib2_compliant(true),
#else
        m_smtlib2_compliant(false),        
#endif
#ifdef Z3DEBUG
        m_copy_params(-1),
#endif
        m_preprocess(true), // temporary hack for disabling all preprocessing..
        m_ignore_checksat(false),
        m_debug_ref_count(false),
        m_trace(false),
        m_trace_file_name("z3.log"),
        m_trace_stream(NULL),
        m_ignore_setparameter(false),
        m_async_commands(true),
        m_display_config(false),
        m_user_theory_preprocess_axioms(false),
        m_user_theory_persist_axioms(false),
        m_nlsat(false) {
    }

    void register_params(ini_params & p);

    void open_trace_file();

    void close_trace_file();

    void copy_params(unsigned idx) {
        m_param_vector->copy_params(this, idx);
    }

    bool has_auto_config(unsigned idx) { return m_auto_config; }

private:

    front_end_params& operator=(front_end_params const& other);
};

#endif /* _FRONT_END_PARAMS_H_ */

