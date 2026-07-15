/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster.h

Abstract:

    Simplifier for "blasting" bit-vectors of size n into bit-vectors of size 1.
    This simplifier only supports concat and extract operators.
    This transformation is useful for handling benchmarks that contain
    many BV equalities.

    Remark: other operators can be mapped into concat/extract by using
    the simplifiers.

Author:

    Leonardo (leonardo) 2011-10-25

--*/
#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/params.h"

class bv1_blaster_simplifier : public dependent_expr_simplifier {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &             m_manager;
        bv_util                   m_util;
        obj_map<func_decl, expr*> m_const2bits;
        ptr_vector<func_decl>     m_newbits;
        ast_ref_vector            m_saved;
        expr_ref                  m_bit1;
        expr_ref                  m_bit0;
        unsigned long long        m_max_memory;
        unsigned                  m_max_steps;

        ast_manager& m() const { return m_manager; }
        bv_util& butil() { return m_util; }
        bv_util const& butil() const { return m_util; }

        void cleanup_buffers() { m_saved.finalize(); }

        rw_cfg(ast_manager& m, params_ref const& p);
        void updt_params(params_ref const& p);
        bool rewrite_patterns() const { return false; }
        bool max_steps_exceeded(unsigned num_steps) const;

        typedef ptr_buffer<expr, 128> bit_buffer;

        void get_bits(expr* arg, bit_buffer& bits);
        void mk_const(func_decl* f, expr_ref& result);
        void blast_bv_term(expr* t, expr_ref& result);
        void reduce_eq(expr* arg1, expr* arg2, expr_ref& result);
        void reduce_ite(expr* c, expr* t, expr* e, expr_ref& result);
        void reduce_num(func_decl* f, expr_ref& result);
        void reduce_extract(func_decl* f, expr* arg, expr_ref& result);
        void reduce_concat(unsigned num, expr* const* args, expr_ref& result);
        void reduce_bin_xor(expr* arg1, expr* arg2, expr_ref& result);
        void reduce_xor(unsigned num_args, expr* const* args, expr_ref& result);

        br_status reduce_app(func_decl* f, unsigned num, expr* const* args,
                             expr_ref& result, proof_ref& result_pr);

        bool reduce_quantifier(quantifier* old_q, expr* new_body,
                               expr* const* new_patterns, expr* const* new_no_patterns,
                               expr_ref& result, proof_ref& result_pr) {
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        rw(ast_manager& m, params_ref const& p) :
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {}
    };

    rw m_rw;

public:
    bv1_blaster_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s)
        : dependent_expr_simplifier(m, s), m_rw(m, p) {}

    char const* name() const override { return "bv1-blast"; }
    void updt_params(params_ref const& p) override { m_rw.cfg().updt_params(p); }
    void collect_param_descrs(param_descrs& r) override;
    void reduce() override;
};

/*
  ADD_SIMPLIFIER("bv1-blast", "reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).", "alloc(bv1_blaster_simplifier, m, p, s)")
*/
