/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    const_intro_rewriter.h

Abstract:

    Rewriter for converting FPA to BV

Author:

    Christoph (cwinter) 2012-02-09

Notes:

--*/

#ifndef _CONST_INTRO_REWRITER_H_
#define _CONST_INTRO_REWRITER_H_

#include"cooperate.h"
#include"bv_decl_plugin.h"
#include"tactic_exception.h"
#include"fpa2bv_converter_prec.h"

struct const_intro_rewriter_cfg : public default_rewriter_cfg {
    ast_manager              & m_manager;        

    expr                     * m_exp;
    func_decl_ref_vector       m_introduced_consts;
    obj_map<func_decl, app*>   m_const2term_map;

    unsigned long long         m_max_memory;
    unsigned                   m_max_steps;

    fpa_util                   m_float_util;

    ast_manager & m() const { return m_manager; }

    const_intro_rewriter_cfg(ast_manager & m, params_ref const & p):
        m_manager(m),
        m_introduced_consts(m),
        m_float_util(m) {
        updt_params(p);
        // We need to make sure that the mananger has the BV plugin loaded.
        symbol s_bv("bv");
        if (!m_manager.has_plugin(s_bv))
            m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));        
    }

    ~const_intro_rewriter_cfg() {
        for (obj_map<func_decl, app*>::iterator it = m_const2term_map.begin();
             it != m_const2term_map.end();
             it++)
        {
            m().dec_ref(it->m_key);
            m().dec_ref(it->m_value);
        }
    }

    void cleanup_buffers() {
    }

    void updt_params(params_ref const & p) {
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_max_steps      = p.get_uint("max_steps", UINT_MAX);        
    }

    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("fpa2bv");
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        TRACE("fpa2bv_rw", tout << "APP: " << f->get_name() << std::endl; );

        if (num == 0 && f->get_family_id() == null_family_id && m_float_util.is_float(f->get_range())) {
    		app * f_cnst = m_manager.mk_const(f);
            if (!m_introduced_consts.contains(f))
			    m_introduced_consts.push_back(f);
            result = f_cnst;
            return BR_DONE;
    	}

        if (f->get_family_id() == m_float_util.get_family_id()) {
            switch (f->get_decl_kind()) {
            case OP_FPA_ADD:
            case OP_FPA_SUB:
            case OP_FPA_NEG:
            case OP_FPA_MUL:
            case OP_FPA_DIV:
            case OP_FPA_REM:
            case OP_FPA_ABS:
            case OP_FPA_MIN:
            case OP_FPA_MAX:
            case OP_FPA_FMA:
            case OP_FPA_SQRT:
            case OP_FPA_TO_FP:
            case OP_FPA_ROUND_TO_INTEGRAL:
				{					
					app * f_app = m_manager.mk_app(f, num, args);
            		result = m_manager.mk_fresh_const(NULL, f->get_range());             	            	
                    func_decl * fd = to_app(result)->get_decl();
					m_introduced_consts.push_back(fd);
                    m_const2term_map.insert_if_not_there(fd, f_app);
                    m().inc_ref(fd);
                    m().inc_ref(f_app);
            		return BR_DONE;
				}
            default:
            	return BR_FAILED;
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

    bool pre_visit(expr * t){
        return true;
    }
};

template class rewriter_tpl<const_intro_rewriter_cfg>;

struct const_intro_rewriter : public rewriter_tpl<const_intro_rewriter_cfg> {
    const_intro_rewriter_cfg m_cfg;
    const_intro_rewriter(ast_manager & m, params_ref const & p):
        rewriter_tpl<const_intro_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
};

#endif
