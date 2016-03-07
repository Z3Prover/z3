/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    fpa2bv_rewriter.h

Abstract:

    Rewriter for converting FPA to BV

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/

#ifndef FPA2BV_REWRITER_H_
#define FPA2BV_REWRITER_H_

#include"rewriter.h"
#include"bv_decl_plugin.h"
#include"fpa2bv_converter.h"

struct fpa2bv_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;
    expr_ref_vector            m_out;
    fpa2bv_converter         & m_conv;
    sort_ref_vector            m_bindings;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    ast_manager & m() const { return m_manager; }

    fpa2bv_rewriter_cfg(ast_manager & m, fpa2bv_converter & c, params_ref const & p);

    ~fpa2bv_rewriter_cfg() {
    }

    void cleanup_buffers() {
        m_out.finalize();
    }

    void reset() {
    }

    void updt_local_params(params_ref const & _p);

    void updt_params(params_ref const & p);

    bool max_steps_exceeded(unsigned num_steps) const;

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);

    bool pre_visit(expr * t);

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr);

};


struct fpa2bv_rewriter : public rewriter_tpl<fpa2bv_rewriter_cfg> {
    fpa2bv_rewriter_cfg m_cfg;
    fpa2bv_rewriter(ast_manager & m, fpa2bv_converter & c, params_ref const & p):
        rewriter_tpl<fpa2bv_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, c, p) {
    }
};

#endif
