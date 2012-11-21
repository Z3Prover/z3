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

#ifndef _FPA2BV_REWRITER_H_
#define _FPA2BV_REWRITER_H_

#include"cooperate.h"
#include"rewriter_def.h"
#include"bv_decl_plugin.h"
#include"fpa2bv_converter.h"

struct fpa2bv_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;    
    expr_ref_vector            m_out;    
    fpa2bv_converter         & m_conv;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    ast_manager & m() const { return m_manager; }

    fpa2bv_rewriter_cfg(ast_manager & m, fpa2bv_converter & c, params_ref const & p):
        m_manager(m),
        m_out(m),
        m_conv(c) {
        updt_params(p);
        // We need to make sure that the mananger has the BV plugin loaded.
        symbol s_bv("bv");
        if (!m_manager.has_plugin(s_bv))
            m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));
    }

    ~fpa2bv_rewriter_cfg() {        
    }

    void cleanup_buffers() {
        m_out.finalize();
    }

    void updt_params(params_ref const & p) {
        m_max_memory     = megabytes_to_bytes(p.get_uint(":max-memory", UINT_MAX));
        m_max_steps      = p.get_uint(":max-steps", UINT_MAX);        
    }

    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("fpa2bv");
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        TRACE("fpa2bv_rw", tout << "APP: " << f->get_name() << std::endl; );

        if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_float(f->get_range())) {
            m_conv.mk_const(f, result);
            return BR_DONE;
        }

		if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_rm_sort(f->get_range())) {
            m_conv.mk_rm_const(f, result);
            return BR_DONE;
        }

        if (m().is_eq(f)) {
            SASSERT(num == 2);
            if (m_conv.is_float(args[0])) {
                m_conv.mk_eq(args[0], args[1], result);
                return BR_DONE;
            }
            return BR_FAILED;
        }

        if (m().is_ite(f)) {
            SASSERT(num == 3);
            if (m_conv.is_float(args[1])) {
                m_conv.mk_ite(args[0], args[1], args[2], result);
                return BR_DONE;
            }
            return BR_FAILED;
        }
        
        if (m_conv.is_float_family(f)) {
            switch (f->get_decl_kind()) {            
            case OP_RM_NEAREST_TIES_TO_AWAY:
            case OP_RM_NEAREST_TIES_TO_EVEN:
            case OP_RM_TOWARD_NEGATIVE:
            case OP_RM_TOWARD_POSITIVE:
			case OP_RM_TOWARD_ZERO: m_conv.mk_rounding_mode(f, result); return BR_DONE;            
            case OP_FLOAT_VALUE: m_conv.mk_value(f, num, args, result); return BR_DONE;                             
            case OP_FLOAT_PLUS_INF: m_conv.mk_plus_inf(f, result); return BR_DONE;
            case OP_FLOAT_MINUS_INF: m_conv.mk_minus_inf(f, result); return BR_DONE;
            case OP_FLOAT_NAN: m_conv.mk_nan(f, result); return BR_DONE;
            case OP_FLOAT_ADD: m_conv.mk_add(f, num, args, result); return BR_DONE;
            case OP_FLOAT_SUB: m_conv.mk_sub(f, num, args, result); return BR_DONE;
            case OP_FLOAT_UMINUS: m_conv.mk_uminus(f, num, args, result); return BR_DONE;
            case OP_FLOAT_MUL: m_conv.mk_mul(f, num, args, result); return BR_DONE;
            case OP_FLOAT_DIV: m_conv.mk_div(f, num, args, result); return BR_DONE;
            case OP_FLOAT_REM: m_conv.mk_remainder(f, num, args, result); return BR_DONE;
            case OP_FLOAT_ABS: m_conv.mk_abs(f, num, args, result); return BR_DONE;
            case OP_FLOAT_MIN: m_conv.mk_min(f, num, args, result); return BR_DONE;
            case OP_FLOAT_MAX: m_conv.mk_max(f, num, args, result); return BR_DONE;
            case OP_FLOAT_FUSED_MA: m_conv.mk_fusedma(f, num, args, result); return BR_DONE;
            case OP_FLOAT_SQRT: m_conv.mk_sqrt(f, num, args, result); return BR_DONE;
            case OP_FLOAT_ROUND_TO_INTEGRAL: m_conv.mk_round_to_integral(f, num, args, result); return BR_DONE;
            case OP_FLOAT_EQ: m_conv.mk_float_eq(f, num, args, result); return BR_DONE;
            case OP_FLOAT_LT: m_conv.mk_float_lt(f, num, args, result); return BR_DONE;
            case OP_FLOAT_GT: m_conv.mk_float_gt(f, num, args, result); return BR_DONE;
            case OP_FLOAT_LE: m_conv.mk_float_le(f, num, args, result); return BR_DONE;
            case OP_FLOAT_GE: m_conv.mk_float_ge(f, num, args, result); return BR_DONE;
            case OP_FLOAT_IS_ZERO: m_conv.mk_is_zero(f, num, args, result); return BR_DONE;
            case OP_FLOAT_IS_NZERO: m_conv.mk_is_nzero(f, num, args, result); return BR_DONE;
            case OP_FLOAT_IS_PZERO: m_conv.mk_is_pzero(f, num, args, result); return BR_DONE;
            case OP_FLOAT_IS_SIGN_MINUS: m_conv.mk_is_sign_minus(f, num, args, result); return BR_DONE;
            case OP_TO_FLOAT: m_conv.mk_to_float(f, num, args, result); return BR_DONE;
            default:
                TRACE("fpa2bv", tout << "unsupported operator: " << f->get_name() << "\n";
                      for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << std::endl;);
                throw tactic_exception("NYI");
            }
        }
        
        return BR_FAILED;
    }

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        return false;
    }

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) { 
        return false; 
    }
};

template class rewriter_tpl<fpa2bv_rewriter_cfg>;

struct fpa2bv_rewriter : public rewriter_tpl<fpa2bv_rewriter_cfg> {
    fpa2bv_rewriter_cfg m_cfg;
    fpa2bv_rewriter(ast_manager & m, fpa2bv_converter & c, params_ref const & p):
        rewriter_tpl<fpa2bv_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),        
        m_cfg(m, c, p) {
    }
};

#endif
