/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    context_params.cpp

Abstract:

    Goodies for managing context parameters in the cmd_context and
    api_context

Author:

    Leonardo (leonardo) 2012-12-01

Notes:

--*/
#include"context_params.h"
#include"gparams.h"
#include"params.h"
#include"ast.h"
#include"solver.h"

context_params::context_params() {
    m_unsat_core     = false;
    m_model          = true;
    m_model_validate = false;
    m_dump_models    = false;
    m_auto_config    = true;
    m_proof          = false;
    m_trace          = false;
    m_debug_ref_count = false;
    m_smtlib2_compliant = false;
    m_well_sorted_check = false;
    m_timeout = UINT_MAX;
    m_rlimit  = UINT_MAX;
    updt_params();
}

void context_params::set_bool(bool & opt, char const * param, char const * value) {
    if (strcmp(value, "true") == 0) {
        opt = true;
    }
    else if (strcmp(value, "false") == 0) {
        opt = false;
    }
    else {
        std::stringstream strm;
        strm << "invalid value '" << value << "' for Boolean parameter '" << param;
        throw default_exception(strm.str());
    }
}

void context_params::set(char const * param, char const * value) {
    std::string p = param;
    unsigned n = static_cast<unsigned>(p.size());
    for (unsigned i = 0; i < n; i++) {
        if (p[i] >= 'A' && p[i] <= 'Z')
            p[i] = p[i] - 'A' + 'a';
        else if (p[i] == '-')
            p[i] = '_';
    }
    if (p == "timeout") {
        long val = strtol(value, 0, 10);
        m_timeout = static_cast<unsigned>(val);
    }
    if (p == "rlimit") {
        long val = strtol(value, 0, 10);
        m_rlimit = static_cast<unsigned>(val);
    }
    else if (p == "type_check" || p == "well_sorted_check") {
        set_bool(m_well_sorted_check, param, value);
    }
    else if (p == "auto_config") {
        set_bool(m_auto_config, param, value);
    }
    else if (p == "proof") {
        set_bool(m_proof, param, value);
    }
    else if (p == "model") {
        set_bool(m_model, param, value);
    }
    else if (p == "model_validate") {
        set_bool(m_model_validate, param, value);
    }
    else if (p == "dump_models") {
        set_bool(m_dump_models, param, value);
    }
    else if (p == "trace") {
        set_bool(m_trace, param, value);
    }
    else if (p == "trace_file_name") {
        m_trace_file_name = value;
    }
    else if (p == "unsat_core") {
        set_bool(m_unsat_core, param, value);
    }
    else if (p == "debug_ref_count") {
        set_bool(m_debug_ref_count, param, value);
    }
    else if (p == "smtlib2_compliant") {
        set_bool(m_smtlib2_compliant, param, value);
    }
    else {
        param_descrs d;
        collect_param_descrs(d);
        std::stringstream strm;
        strm << "unknown parameter '" << p << "'\n";
        strm << "Legal parameters are:\n";
        d.display(strm, 2, false, false);
        throw default_exception(strm.str());        
    }
}

void context_params::updt_params() {
    updt_params(gparams::get());
}

void context_params::updt_params(params_ref const & p) {
    m_timeout           = p.get_uint("timeout", m_timeout);
    m_rlimit            = p.get_uint("rlimit", m_rlimit);
    m_well_sorted_check = p.get_bool("type_check", p.get_bool("well_sorted_check", m_well_sorted_check));
    m_auto_config       = p.get_bool("auto_config", m_auto_config);
    m_proof             = p.get_bool("proof", m_proof);
    m_model             = p.get_bool("model", m_model);
    m_model_validate    = p.get_bool("model_validate", m_model_validate);
    m_dump_models       = p.get_bool("dump_models", m_dump_models);
    m_trace             = p.get_bool("trace", m_trace);
    m_trace_file_name   = p.get_str("trace_file_name", "z3.log");
    m_unsat_core        = p.get_bool("unsat_core", m_unsat_core);
    m_debug_ref_count   = p.get_bool("debug_ref_count", m_debug_ref_count);
    m_smtlib2_compliant = p.get_bool("smtlib2_compliant", m_smtlib2_compliant);
}

void context_params::collect_param_descrs(param_descrs & d) {
    d.insert("timeout", CPK_UINT, "default timeout (in milliseconds) used for solvers", "4294967295");
    d.insert("rlimit", CPK_UINT, "default resource limit used for solvers", "4294967295");
    d.insert("well_sorted_check", CPK_BOOL, "type checker", "false");
    d.insert("type_check", CPK_BOOL, "type checker (alias for well_sorted_check)", "true");
    d.insert("auto_config", CPK_BOOL, "use heuristics to automatically select solver and configure it", "true");
    d.insert("model_validate", CPK_BOOL, "validate models produced by solvers", "false");
    d.insert("dump_models", CPK_BOOL, "dump models whenever check-sat returns sat", "false");
    d.insert("trace", CPK_BOOL, "trace generation for VCC", "false");
    d.insert("trace_file_name", CPK_STRING, "trace out file name (see option 'trace')", "z3.log");
    d.insert("debug_ref_count", CPK_BOOL, "debug support for AST reference counting", "false");
    d.insert("smtlib2_compliant", CPK_BOOL, "enable/disable SMT-LIB 2.0 compliance", "false");
    collect_solver_param_descrs(d);
}

void context_params::collect_solver_param_descrs(param_descrs & d) {
    d.insert("proof", CPK_BOOL, "proof generation, it must be enabled when the Z3 context is created", "false");
    d.insert("model", CPK_BOOL, "model generation for solvers, this parameter can be overwritten when creating a solver", "true");
    d.insert("unsat_core", CPK_BOOL, "unsat-core generation for solvers, this parameter can be overwritten when creating a solver, not every solver in Z3 supports unsat core generation", "false");
}

params_ref context_params::merge_default_params(params_ref const & p) {
    if (!m_auto_config && !p.contains("auto_config")) {
        params_ref new_p = p;
        new_p.set_bool("auto_config", false);
        return new_p;
    }
    else {
        return p;
    }
}

void context_params::get_solver_params(ast_manager const & m, params_ref & p, bool & proofs_enabled, bool & models_enabled, bool & unsat_core_enabled) {
    proofs_enabled     = m.proofs_enabled() && p.get_bool("proof", m_proof);
    models_enabled     = p.get_bool("model", m_model);
    unsat_core_enabled = p.get_bool("unsat_core", m_unsat_core);
    p = merge_default_params(p);
}

ast_manager * context_params::mk_ast_manager() {
    ast_manager * r = alloc(ast_manager, 
                            m_proof ? PGM_FINE : PGM_DISABLED, 
                            m_trace ? m_trace_file_name.c_str() : 0);
    if (m_smtlib2_compliant)
        r->enable_int_real_coercions(false);
    if (m_debug_ref_count)
        r->debug_ref_count();
    return r;
}


