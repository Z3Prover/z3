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

#include"cooperate.h"
#include"rewriter_def.h"
#include"bv_decl_plugin.h"
#include"fpa2bv_converter.h"
#include"fpa2bv_rewriter_params.hpp"

struct fpa2bv_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;    
    expr_ref_vector            m_out;    
    fpa2bv_converter         & m_conv;
    sort_ref_vector            m_bindings;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    ast_manager & m() const { return m_manager; }

    fpa2bv_rewriter_cfg(ast_manager & m, fpa2bv_converter & c, params_ref const & p) :
        m_manager(m),
        m_out(m),
        m_conv(c),
        m_bindings(m) {
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

    void reset() {
    }

    void updt_local_params(params_ref const & _p) {
        fpa2bv_rewriter_params p(_p);
        bool v = p.hi_fp_unspecified();
        m_conv.set_unspecified_fp_hi(v);
    }

    void updt_params(params_ref const & p) {
        m_max_memory        = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_max_steps         = p.get_uint("max_steps", UINT_MAX);
        updt_local_params(p);
    }

    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("fpa2bv");
        return num_steps > m_max_steps;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        TRACE("fpa2bv_rw", tout << "APP: " << f->get_name() << std::endl; );

        if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_float(f->get_range())) {
            m_conv.mk_const(f, result);
            return BR_DONE;
        }

        if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_rm(f->get_range())) {
            m_conv.mk_rm_const(f, result);
            return BR_DONE;
        }

        if (m().is_eq(f)) {
            SASSERT(num == 2);
            TRACE("fpa2bv_rw", tout << "(= " << mk_ismt2_pp(args[0], m()) << " " << 
                                                mk_ismt2_pp(args[1], m()) << ")" << std::endl;);
            SASSERT(m().get_sort(args[0]) == m().get_sort(args[1]));            
            sort * ds = f->get_domain()[0];
            if (m_conv.is_float(ds)) {
                m_conv.mk_eq(args[0], args[1], result);
                return BR_DONE;
            }
            else if (m_conv.is_rm(ds)) {
                result = m().mk_eq(args[0], args[1]);
                return BR_DONE;
            }
            return BR_FAILED;
        }
        else if (m().is_ite(f)) {
            SASSERT(num == 3);
            if (m_conv.is_float(args[1])) {
                m_conv.mk_ite(args[0], args[1], args[2], result);
                return BR_DONE;
            }
            return BR_FAILED;
        }
        else if (m().is_distinct(f)) {
            sort * ds = f->get_domain()[0];
            if (m_conv.is_float(ds) || m_conv.is_rm(ds)) {
                m_conv.mk_distinct(f, num, args, result);
                return BR_DONE;
            }
            return BR_FAILED;
        }
        
        if (m_conv.is_float_family(f)) {
            switch (f->get_decl_kind()) {
            case OP_FPA_RM_NEAREST_TIES_TO_AWAY:
            case OP_FPA_RM_NEAREST_TIES_TO_EVEN:
            case OP_FPA_RM_TOWARD_NEGATIVE:
            case OP_FPA_RM_TOWARD_POSITIVE:
            case OP_FPA_RM_TOWARD_ZERO: m_conv.mk_rounding_mode(f, result); return BR_DONE;
            case OP_FPA_NUM: m_conv.mk_numeral(f, num, args, result); return BR_DONE;                             
            case OP_FPA_PLUS_INF: m_conv.mk_pinf(f, result); return BR_DONE;
            case OP_FPA_MINUS_INF: m_conv.mk_ninf(f, result); return BR_DONE;
            case OP_FPA_PLUS_ZERO: m_conv.mk_pzero(f, result); return BR_DONE;
            case OP_FPA_MINUS_ZERO: m_conv.mk_nzero(f, result); return BR_DONE;
            case OP_FPA_NAN: m_conv.mk_nan(f, result); return BR_DONE;
            case OP_FPA_ADD: m_conv.mk_add(f, num, args, result); return BR_DONE;
            case OP_FPA_SUB: m_conv.mk_sub(f, num, args, result); return BR_DONE;
            case OP_FPA_NEG: m_conv.mk_neg(f, num, args, result); return BR_DONE;
            case OP_FPA_MUL: m_conv.mk_mul(f, num, args, result); return BR_DONE;
            case OP_FPA_DIV: m_conv.mk_div(f, num, args, result); return BR_DONE;
            case OP_FPA_REM: m_conv.mk_rem(f, num, args, result); return BR_DONE;
            case OP_FPA_ABS: m_conv.mk_abs(f, num, args, result); return BR_DONE;            
            case OP_FPA_FMA: m_conv.mk_fma(f, num, args, result); return BR_DONE;
            case OP_FPA_SQRT: m_conv.mk_sqrt(f, num, args, result); return BR_DONE;
            case OP_FPA_ROUND_TO_INTEGRAL: m_conv.mk_round_to_integral(f, num, args, result); return BR_DONE;
            case OP_FPA_EQ: m_conv.mk_float_eq(f, num, args, result); return BR_DONE;
            case OP_FPA_LT: m_conv.mk_float_lt(f, num, args, result); return BR_DONE;
            case OP_FPA_GT: m_conv.mk_float_gt(f, num, args, result); return BR_DONE;
            case OP_FPA_LE: m_conv.mk_float_le(f, num, args, result); return BR_DONE;
            case OP_FPA_GE: m_conv.mk_float_ge(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_ZERO: m_conv.mk_is_zero(f, num, args, result); return BR_DONE;            
            case OP_FPA_IS_NAN: m_conv.mk_is_nan(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_INF: m_conv.mk_is_inf(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_NORMAL: m_conv.mk_is_normal(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_SUBNORMAL: m_conv.mk_is_subnormal(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_POSITIVE: m_conv.mk_is_positive(f, num, args, result); return BR_DONE;
            case OP_FPA_IS_NEGATIVE: m_conv.mk_is_negative(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_FP: m_conv.mk_to_fp(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_FP_UNSIGNED: m_conv.mk_to_fp_unsigned(f, num, args, result); return BR_DONE;
            case OP_FPA_FP: m_conv.mk_fp(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_UBV: m_conv.mk_to_ubv(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_SBV: m_conv.mk_to_sbv(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_REAL: m_conv.mk_to_real(f, num, args, result); return BR_DONE;
            case OP_FPA_TO_IEEE_BV: m_conv.mk_to_ieee_bv(f, num, args, result); return BR_DONE;
            
            case OP_FPA_MIN: m_conv.mk_min(f, num, args, result); return BR_REWRITE_FULL;
            case OP_FPA_MAX: m_conv.mk_max(f, num, args, result); return BR_REWRITE_FULL;

            case OP_FPA_INTERNAL_MIN_UNSPECIFIED: result = m_conv.mk_min_unspecified(f, args[0], args[1]); return BR_DONE;
            case OP_FPA_INTERNAL_MAX_UNSPECIFIED: result = m_conv.mk_max_unspecified(f, args[0], args[1]); return BR_DONE;
            case OP_FPA_INTERNAL_MIN_I: m_conv.mk_min_i(f, num, args, result); return BR_DONE;
            case OP_FPA_INTERNAL_MAX_I: m_conv.mk_max_i(f, num, args, result); return BR_DONE;

            case OP_FPA_INTERNAL_RM:
            case OP_FPA_INTERNAL_BVWRAP: 
            case OP_FPA_INTERNAL_BVUNWRAP:                
            case OP_FPA_INTERNAL_TO_REAL_UNSPECIFIED:
            case OP_FPA_INTERNAL_TO_UBV_UNSPECIFIED: 
            case OP_FPA_INTERNAL_TO_SBV_UNSPECIFIED: return BR_FAILED;
            default:
                TRACE("fpa2bv", tout << "unsupported operator: " << f->get_name() << "\n";
                      for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << std::endl;);
                NOT_IMPLEMENTED_YET();
            }
        }
        else {
            SASSERT(!m_conv.is_float_family(f));
            bool is_float_uf = m_conv.is_float(f->get_range()) || m_conv.is_rm(f->get_range());

            for (unsigned i = 0; i < f->get_arity(); i++) {
                sort * di = f->get_domain()[i];
                is_float_uf |= m_conv.is_float(di) || m_conv.is_rm(di);
            }

            if (is_float_uf) {
                m_conv.mk_uninterpreted_function(f, num, args, result);
                return BR_DONE;
            }
        }

        return BR_FAILED;
    }

    bool pre_visit(expr * t)
    {
        TRACE("fpa2bv", tout << "pre_visit: " << mk_ismt2_pp(t, m()) << std::endl;);

        if (is_quantifier(t)) {            
            quantifier * q = to_quantifier(t);            
            TRACE("fpa2bv", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m()) << std::endl;);
            sort_ref_vector new_bindings(m_manager);
            for (unsigned i = 0 ; i < q->get_num_decls(); i++)
                new_bindings.push_back(q->get_decl_sort(i));
            SASSERT(new_bindings.size() == q->get_num_decls());
            m_bindings.append(new_bindings);
        }
        return true;
    }

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        unsigned curr_sz   = m_bindings.size();
        SASSERT(old_q->get_num_decls() <= curr_sz);
        unsigned num_decls = old_q->get_num_decls();
        unsigned old_sz    = curr_sz - num_decls;
        string_buffer<> name_buffer;
        ptr_buffer<sort> new_decl_sorts;
        sbuffer<symbol>  new_decl_names;
        for (unsigned i = 0; i < num_decls; i++) {
            symbol const & n = old_q->get_decl_name(i);
            sort * s         = old_q->get_decl_sort(i);
            if (m_conv.is_float(s)) {
                unsigned ebits = m_conv.fu().get_ebits(s);
                unsigned sbits = m_conv.fu().get_sbits(s);
                name_buffer.reset();
                name_buffer << n << ".bv";
                new_decl_names.push_back(symbol(name_buffer.c_str()));
                new_decl_sorts.push_back(m_conv.bu().mk_sort(sbits+ebits)); 
            }
            else {
                new_decl_sorts.push_back(s);
                new_decl_names.push_back(n);
            }
        }
        result = m().mk_quantifier(old_q->is_forall(), new_decl_sorts.size(), new_decl_sorts.c_ptr(), new_decl_names.c_ptr(),
                                   new_body, old_q->get_weight(), old_q->get_qid(), old_q->get_skid(),
                                   old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns);
        result_pr = 0;
        m_bindings.shrink(old_sz);        
        TRACE("fpa2bv", tout << "reduce_quantifier[" << old_q->get_depth() << "]: " << 
                mk_ismt2_pp(old_q->get_expr(), m()) << std::endl <<
                " new body: " << mk_ismt2_pp(new_body, m()) << std::endl;
                tout << "result = " << mk_ismt2_pp(result, m()) << std::endl;);                
        return true;
    }

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) { 
        if (t->get_idx() >= m_bindings.size())
            return false;
        // unsigned inx = m_bindings.size() - t->get_idx() - 1;        

        expr_ref new_exp(m());
        sort * s = t->get_sort();
        if (m_conv.is_float(s))
        {
            expr_ref new_var(m());
            unsigned ebits = m_conv.fu().get_ebits(s);
            unsigned sbits = m_conv.fu().get_sbits(s);
            new_var = m().mk_var(t->get_idx(), m_conv.bu().mk_sort(sbits+ebits));
            m_conv.mk_fp(m_conv.bu().mk_extract(sbits+ebits-1, sbits+ebits-1, new_var),
                         m_conv.bu().mk_extract(ebits - 1, 0, new_var),
                         m_conv.bu().mk_extract(sbits+ebits-2, ebits, new_var),                         
                         new_exp);
        }
        else
            new_exp = m().mk_var(t->get_idx(), s);

        result = new_exp;
        result_pr = 0;        
        TRACE("fpa2bv", tout << "reduce_var: " << mk_ismt2_pp(t, m()) << " -> " << mk_ismt2_pp(result, m()) << std::endl;);
        return true;
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
