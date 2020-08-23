/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    context_params.h

Abstract:

    Goodies for managing context parameters in the cmd_context and
    api_context

Author:

    Leonardo (leonardo) 2012-12-01

Notes:

--*/
#pragma once

#include "util/params.h"
class ast_manager;

class context_params {
    void set_bool(bool & opt, char const * param, char const * value);
    void set_uint(unsigned & opt, char const * param, char const * value);

    unsigned    m_rlimit { 0 };
    ast_manager* m_manager { nullptr };

public:
    bool        m_auto_config { true };
    bool        m_proof { false };
    std::string m_dot_proof_file;
    bool        m_debug_ref_count { false };
    bool        m_trace { false };
    std::string m_trace_file_name;
    bool        m_well_sorted_check { false };
    bool        m_model { true };
    bool        m_model_validate { false };
    bool        m_dump_models { false };
    bool        m_unsat_core { false };
    bool        m_smtlib2_compliant { false }; // it must be here because it enable/disable the use of coercions in the ast_manager.
    unsigned    m_timeout { UINT_MAX } ;
    bool        m_statistics { false };

    unsigned rlimit() const { return m_rlimit; }
    context_params();
    void set(char const * param, char const * value);
    void set_rlimit(unsigned lim) { m_rlimit = lim; }
    void updt_params();
    void updt_params(params_ref const & p);
    static void collect_param_descrs(param_descrs & d);
    /*
      REG_PARAMS('context_params::collect_param_descrs')
    */

    /**
       \brief Goodies for extracting parameters for creating a solver object.
    */
    void get_solver_params(ast_manager const & m, params_ref & p, bool & proofs_enabled, bool & models_enabled, bool & unsat_core_enabled);

    static void collect_solver_param_descrs(param_descrs & d);

    /**
       \brief Include in p parameters derived from this context_params.
       These are parameters that are meaningful for tactics and solvers.
       Example: auto_config
    */
    params_ref merge_default_params(params_ref const & p);

    /**
       \brief Create an AST manager using this configuration.
    */
    ast_manager * mk_ast_manager();

    void set_foreign_manager(ast_manager* m) { m_manager = m; }
    bool owns_manager() const { return m_manager != nullptr; }
};


