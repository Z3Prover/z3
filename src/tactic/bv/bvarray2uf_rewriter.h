/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bvarray2uf_rewriter.h

Abstract:

    Rewriter that rewrites bit-vector arrays into bit-vector
    (uninterpreted) functions.

Author:

    Christoph (cwinter) 2015-11-04

Notes:

--*/
#ifndef BVARRAY2UF_REWRITER_H_
#define BVARRAY2UF_REWRITER_H_

#include"rewriter.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"

class bvarray2uf_rewriter_cfg : public default_rewriter_cfg {
    ast_manager       & m_manager;
    expr_ref_vector     m_out;
    sort_ref_vector     m_bindings;
    bv_util             m_bv_util;
    array_util          m_array_util;
    extension_model_converter * m_emc;
    filter_model_converter * m_fmc;

    obj_map<expr, func_decl*> m_arrays_fs;

public:
    bvarray2uf_rewriter_cfg(ast_manager & m, params_ref const & p);
    ~bvarray2uf_rewriter_cfg();

    ast_manager & m() const { return m_manager; }
    void updt_params(params_ref const & p) {}

    void reset();

    bool pre_visit(expr * t);

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr);

    expr_ref_vector extra_assertions;

    void set_mcs(extension_model_converter * emc, filter_model_converter * fmc) { m_emc = emc; m_fmc = fmc; }

protected:
    sort * get_index_sort(expr * e);
    sort * get_index_sort(sort * s);
    sort * get_value_sort(expr * e);
    sort * get_value_sort(sort * s);
    bool is_bv_array(expr * e);
    bool is_bv_array(sort * e);
    func_decl_ref mk_uf_for_array(expr * e);
};


struct bvarray2uf_rewriter : public rewriter_tpl<bvarray2uf_rewriter_cfg> {
    bvarray2uf_rewriter_cfg m_cfg;
    bvarray2uf_rewriter(ast_manager & m, params_ref const & p) :
        rewriter_tpl<bvarray2uf_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }

    void set_mcs(extension_model_converter * emc, filter_model_converter * fmc) { m_cfg.set_mcs(emc, fmc); }
};

#endif

