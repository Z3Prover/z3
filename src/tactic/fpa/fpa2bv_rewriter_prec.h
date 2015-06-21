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
#include"fpa2bv_converter_prec.h"
#include"tactic_exception.h"
#include <vector>

struct fpa2bv_rewriter_prec_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;    
    expr_ref_vector            m_out; 
    fpa2bv_converter_prec    & m_conv;
    obj_map<func_decl,unsigned> * cnst2prec_map;

    unsigned precision;
    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    ast_manager & m() const { return m_manager; }

    fpa2bv_rewriter_prec_cfg(ast_manager & m,  fpa2bv_converter_prec & c, params_ref const & p):
        m_manager(m),
        m_out(m),
        m_conv(c) {
        updt_params(p);
        // We need to make sure that the mananger has the BV plugin loaded.
        symbol s_bv("bv");
        if (!m_manager.has_plugin(s_bv))
            m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));
    }

    ~fpa2bv_rewriter_prec_cfg() {
    }

    void cleanup_buffers() {
        m_out.finalize();
    }

    unsigned get_precision(func_decl * f){
    	if(cnst2prec_map->contains(f))
    		return cnst2prec_map->find(f);
    	else return precision;
    }
    void set_precision(unsigned p) { precision=p; }
    void set_mappings(obj_map<func_decl,unsigned> * o2p)
    {
    	this->cnst2prec_map=o2p;
    }

    void updt_params(params_ref const & p) {
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_max_steps      = p.get_uint("max_steps", UINT_MAX);        
    }

    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("fpa2bv");
                return num_steps > m_max_steps;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    	TRACE("fpa2bv_rw", tout << "APP: " << f->get_name() << std::endl; );

    	if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_float(f->get_range())) {
    		m_conv.mk_const(f, get_precision(f), result);
    		return BR_DONE;
    	}

    	if (num == 0 && f->get_family_id() == null_family_id && m_conv.is_rm(f->get_range())) {
    		m_conv.mk_rm_const(f, result);
    		return BR_DONE;
    	}

        if (m().is_eq(f)) {
            SASSERT(num == 2);
            //SASSERT(m().get_sort(args[0]) == m().get_sort(args[1]));
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

    	if (m().is_ite(f)) {
    		SASSERT(num == 3);
    		if (m_conv.is_float(args[1])) {
    			m_conv.mk_ite(args[0], args[1], args[2], result);
    			return BR_DONE;
    		}
    		return BR_FAILED;
    	}

    	expr_ref  newAssertion(m_manager);

    	if (m_conv.is_float_family(f))
    	{
    		switch (f->get_decl_kind())
    		{
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
    		case OP_FPA_ADD:
    			m_conv.mk_add(f,get_precision(f), num, args, result);return BR_DONE;
    		case OP_FPA_SUB:
    			m_conv.mk_sub(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_NEG:
    			m_conv.mk_uminus(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_MUL:
    			m_conv.mk_mul(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_DIV:
    			m_conv.mk_div(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_REM:
    			m_conv.mk_remainder(f, get_precision(f), num, args, result); return BR_DONE;
			case OP_FPA_ABS: m_conv.mk_abs(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_MIN: m_conv.mk_min(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_MAX: m_conv.mk_max(f, get_precision(f), num, args, result); return BR_DONE;    		
			case OP_FPA_FMA:
    			m_conv.mk_fusedma(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_SQRT:
    			m_conv.mk_sqrt(f, get_precision(f), num, args, result); return BR_DONE;
    		case OP_FPA_ROUND_TO_INTEGRAL: m_conv.mk_round_to_integral(f,  get_precision(f), num, args, result); return BR_DONE;
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

        if (f->get_family_id() == null_family_id)
        {
            bool is_float_uf = m_conv.is_float(f->get_range());
            unsigned i = 0;
            while (!is_float_uf && i < num)
            {
                is_float_uf = m_conv.is_float(f->get_domain()[i]);
                i++;
            }

            if (is_float_uf)
            {
                m_conv.mk_uninterpreted_function(f, num, args, result);
                return BR_DONE;
            }
        }
        
        return BR_FAILED;
    }

    bool pre_visit(expr * t)
    {
    	 TRACE("pre_visit_prec", tout << mk_ismt2_pp(t, m()) << std::endl;);
    	 
    	 if(t->get_kind() == AST_APP && is_app_of(t, to_app(t)->get_family_id(), OP_EQ)) {
    	     //Equation over non-boolean expressions, it should be of form constantI = subexprI
    		 app * a = to_app(t);

             if (a->get_num_args() == 2) {
                 expr * a0 = a->get_arg(0);
                 expr * a1 = a->get_arg(1);
                 func_decl * cnst = 0;

                 if (a0->get_kind() == AST_APP && cnst2prec_map->contains(to_app(a0)->get_decl()))
                     cnst = to_app(a0)->get_decl();
                 else if (a1->get_kind() == AST_APP && cnst2prec_map->contains(to_app(a1)->get_decl()))
                     cnst = to_app(a1)->get_decl();
    		 
                 if (cnst == 0) {
                     // For all equalities that were in the original problem, we don't
                     // have any precision tracking, so those simply get 100% precision.
                     set_precision(100);
                 }
                 else
                     set_precision(cnst2prec_map->find(cnst));
                 TRACE("pre_visit_prec", tout << "Precision = " << get_precision(NULL) << std::endl;);
             }
    	 }
         return true;
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

template class rewriter_tpl<fpa2bv_rewriter_prec_cfg>;

struct fpa2bv_rewriter_prec : public rewriter_tpl<fpa2bv_rewriter_prec_cfg> {
    fpa2bv_rewriter_prec_cfg m_cfg;
    fpa2bv_rewriter_prec(ast_manager & m, fpa2bv_converter_prec & c, params_ref const & p):
        rewriter_tpl<fpa2bv_rewriter_prec_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, c, p) {
    }
};

#endif
