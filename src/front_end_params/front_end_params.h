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

#include"ast.h"
#include"preprocessor_params.h"
#include"smt_params.h"
#include"arith_simplifier_params.h"

struct front_end_params : public preprocessor_params, public smt_params, 
                          public arith_simplifier_params {
    bool                m_at_labels_cex; // only use labels which contains the @ symbol when building multiple counterexamples.
    bool                m_check_at_labels; // check that @ labels are inserted to generate unique counter-examples.
    bool                m_well_sorted_check;
    unsigned            m_memory_high_watermark;
    unsigned            m_memory_max_size;
    proof_gen_mode      m_proof_mode;
    bool                m_auto_config;

    bool                m_debug_ref_count;
    bool                m_trace;
    std::string         m_trace_file_name;
    std::fstream*       m_trace_stream;
    bool                m_display_config;
    bool                m_nlsat; // temporary hack until strategic_solver is ported to new tactic framework

    bool                m_dump_goal_as_smt;

    front_end_params():
        m_at_labels_cex(false),
        m_check_at_labels(false),
        m_well_sorted_check(true),
        m_memory_high_watermark(0),
        m_memory_max_size(0),
        m_proof_mode(PGM_DISABLED),
#if    defined(SMTCOMP) || defined(_EXTERNAL_RELEASE)
        m_auto_config(true),
#else
        m_auto_config(false), 
#endif
        m_debug_ref_count(false),
        m_trace(false),
        m_trace_file_name("z3.log"),
        m_trace_stream(NULL),
        m_display_config(false),
        m_nlsat(false),
        m_dump_goal_as_smt(false) {
    }

    void open_trace_file();

    void close_trace_file();

    bool has_auto_config(unsigned idx) { return m_auto_config; }

private:

    front_end_params& operator=(front_end_params const& other);
};

#endif /* _FRONT_END_PARAMS_H_ */

