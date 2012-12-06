/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    th_rewriter.h

Abstract:

    Rewriter for applying all builtin (cheap) theory rewrite rules.

Author:

    Leonardo (leonardo) 2011-04-07

Notes:

--*/
#ifndef _TH_REWRITER_H_
#define _TH_REWRITER_H_

#include"ast.h"
#include"rewriter_types.h"
#include"params.h"

class expr_substitution;

class th_rewriter {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    th_rewriter(ast_manager & m, params_ref const & p = params_ref());
    ~th_rewriter();

    ast_manager & m () const;

    void updt_params(params_ref const & p);
    static void get_param_descrs(param_descrs & r);
    unsigned get_cache_size() const;
    unsigned get_num_steps() const;

    void operator()(expr_ref& term);
    void operator()(expr * t, expr_ref & result);
    void operator()(expr * t, expr_ref & result, proof_ref & result_pr);
    void operator()(expr * n, unsigned num_bindings, expr * const * bindings, expr_ref & result);

    void cancel() { set_cancel(true); }
    void reset_cancel() { set_cancel(false); }
    void set_cancel(bool f);
    void cleanup();
    void reset();

    void set_substitution(expr_substitution * s);
    
    // Dependency tracking is very coarse. 
    // The rewriter just keeps accumulating the dependencies of the used substitutions.
    // The following methods are used to recover and reset them.
    // Remark: reset_used_dependecies will reset the internal cache if get_used_dependencies() != 0
    expr_dependency * get_used_dependencies();
    void reset_used_dependencies();
};

#endif
