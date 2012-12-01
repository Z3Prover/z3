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
    smt_params::register_params(p);
    arith_simplifier_params::register_params(p);
    p.register_bool_param("at_labels_cex", m_at_labels_cex, 
                          "only use labels that contain '@' when building multiple counterexamples");
    p.register_bool_param("check_at_labels", m_check_at_labels, 
                          "check that labels containing '@' are used correctly to only produce unique counter examples");
    p.register_bool_param("default_qid", m_default_qid, "create a default quantifier id based on its position, the id is used to report profiling information (see QI_PROFILE)");
    
    p.register_bool_param("type_check", m_well_sorted_check, "enable/disable type checker");
    p.register_bool_param("well_sorted_check", m_well_sorted_check, "enable/disable type checker");
    p.register_unsigned_param("soft_timeout", m_soft_timeout, "set approximate timeout for each solver query (milliseconds), the value 0 represents no timeout", true);
    p.register_double_param("instruction_max", m_instr_out, "set the (approximate) maximal number of instructions per invocation of check", true);
    p.register_bool_param("auto_config", m_auto_config, "use heuristics to set Z3 configuration parameters, it is only available for the SMT-LIB input format");
    p.register_int_param("proof_mode", 0, 2, reinterpret_cast<int&>(m_proof_mode), "select proof generation mode: 0 - disabled, 1 - coarse grain, 2 - fine grain");
    p.register_bool_param("trace", m_trace, "enable tracing for the Axiom Profiler tool");
    p.register_string_param("trace_file_name", m_trace_file_name, "tracing file name");
    p.register_bool_param("display_config", m_display_config, "display configuration used by Z3");

#ifdef _WINDOWS
    // The non-windows memory manager does not have access to memory sizes.
    p.register_unsigned_param("memory_high_watermark", m_memory_high_watermark, 
                              "set high watermark for memory consumption (in megabytes)");
    p.register_unsigned_param("memory_max_size", m_memory_max_size,
                              "set hard upper limit for memory consumption (in megabytes)");
#endif


    PRIVATE_PARAMS({
        p.register_bool_param("ignore_checksat", m_ignore_checksat);
        p.register_bool_param("debug_ref_count", m_debug_ref_count);
        p.register_bool_param("incremental_core_assert", m_incremental_core_assert);
        DEBUG_CODE(p.register_int_param("copy_params", m_copy_params););
    });

    // temporary hack until strategic_solver is ported to new tactic framework
    PRIVATE_PARAMS({
        p.register_bool_param("nlsat", m_nlsat);
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
