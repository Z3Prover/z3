/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    front_end_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-05-10.

Revision History:

--*/
#include"front_end_params.h"

void front_end_params::register_params(ini_params & p) {
    p.register_param_vector(m_param_vector.get());
    preprocessor_params::register_params(p);
    spc_params::register_params(p);
    smt_params::register_params(p);
    parser_params::register_params(p);
    arith_simplifier_params::register_params(p);
    p.register_int_param("ENGINE", 0, 2, reinterpret_cast<int&>(m_engine), "0: SMT solver, 1: Superposition prover, 2: EPR solver, true");
    z3_solver_params::register_params(p);
    model_params::register_params(p);
    p.register_unsigned_param("MAX_COUNTEREXAMPLES", m_max_num_cex, 
                              "set the maximum number of counterexamples when using Simplify front end");
    p.register_bool_param("AT_LABELS_CEX", m_at_labels_cex, 
                          "only use labels that contain '@' when building multiple counterexamples");
    p.register_bool_param("CHECK_AT_LABELS", m_check_at_labels, 
                          "check that labels containing '@' are used correctly to only produce unique counter examples");
    p.register_bool_param("DEFAULT_QID", m_default_qid, "create a default quantifier id based on its position, the id is used to report profiling information (see QI_PROFILE)");
    
    p.register_bool_param("TYPE_CHECK", m_well_sorted_check, "enable/disable type checker");
    p.register_bool_param("WELL_SORTED_CHECK", m_well_sorted_check, "enable/disable type checker");
    p.register_bool_param("INTERACTIVE", m_interactive, "enable interactive mode using Simplify input format");
    p.register_unsigned_param("SOFT_TIMEOUT", m_soft_timeout, "set approximate timeout for each solver query (milliseconds), the value 0 represents no timeout", true);
    p.register_double_param("INSTRUCTION_MAX", m_instr_out, "set the (approximate) maximal number of instructions per invocation of check", true);
    p.register_bool_param("AUTO_CONFIG", m_auto_config, "use heuristics to set Z3 configuration parameters, it is only available for the SMT-LIB input format");
    p.register_int_param("PROOF_MODE", 0, 2, reinterpret_cast<int&>(m_proof_mode), "select proof generation mode: 0 - disabled, 1 - coarse grain, 2 - fine grain");
    p.register_bool_param("TRACE", m_trace, "enable tracing for the Axiom Profiler tool");
    p.register_string_param("TRACE_FILE_NAME", m_trace_file_name, "tracing file name");
    p.register_bool_param("IGNORE_SETPARAMETER", m_ignore_setparameter, "ignore (SETPARAMETER ...) commands in Simplify format input");
    p.register_bool_param("ASYNC_COMMANDS", m_async_commands, "enable/disable support for asynchronous commands in the Simplify front-end.");
    p.register_bool_param("DISPLAY_CONFIG", m_display_config, "display configuration used by Z3");

#ifdef _WINDOWS
    // The non-windows memory manager does not have access to memory sizes.
    p.register_unsigned_param("MEMORY_HIGH_WATERMARK", m_memory_high_watermark, 
                              "set high watermark for memory consumption (in megabytes)");
    p.register_unsigned_param("MEMORY_MAX_SIZE", m_memory_max_size,
                              "set hard upper limit for memory consumption (in megabytes)");
#endif

#ifndef _EXTERNAL_RELEASE
    // external users should not have access to it.
    p.register_bool_param("PREPROCESS", m_preprocess);
#endif

    p.register_bool_param("USER_THEORY_PREPROCESS_AXIOMS", 
                          m_user_theory_preprocess_axioms, 
                          "Apply full pre-processing to user theory axioms",
                          true);

    p.register_bool_param("USER_THEORY_PERSIST_AXIOMS",
                          m_user_theory_persist_axioms,
                          "Persist user axioms to the base level",
                          true);

    p.register_bool_param("SMTLIB2_COMPLIANT", m_smtlib2_compliant);    

    p.register_bool_param("IGNORE_BAD_PATTERNS", m_ignore_bad_patterns);

    PRIVATE_PARAMS({
        p.register_bool_param("IGNORE_CHECKSAT", m_ignore_checksat);
        p.register_bool_param("DEBUG_REF_COUNT", m_debug_ref_count);
        p.register_bool_param("IGNORE_USER_PATTERNS", m_ignore_user_patterns);
        p.register_bool_param("INCREMENTAL_CORE_ASSERT", m_incremental_core_assert);
        DEBUG_CODE(p.register_int_param("COPY_PARAMS", m_copy_params););
    });

    // temporary hack until strategic_solver is ported to new tactic framework
    PRIVATE_PARAMS({
        p.register_bool_param("NLSAT", m_nlsat);
    });
}

void front_end_params::open_trace_file() {
    if (m_trace) {
        m_trace_stream = alloc(std::fstream, m_trace_file_name.c_str(), std::ios_base::out);
    }
}

void front_end_params::close_trace_file() {
    if (m_trace_stream != NULL) {
        std::fstream &tmp = *m_trace_stream;
        m_trace_stream = NULL;
        tmp << "[eof]\n";
        tmp.close();
        // do not delete it, this might be called from a Ctrl-C signal handler
        // and there might be someone writing to it
    }
}
