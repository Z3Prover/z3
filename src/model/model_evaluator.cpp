/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator.cpp

Abstract:

    Evaluate expressions in a given model.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include"model.h"
#include"model_evaluator_params.hpp"
#include"rewriter_types.h"
#include"model_evaluator.h"
#include"bool_rewriter.h"
#include"arith_rewriter.h"
#include"bv_rewriter.h"
#include"pb_rewriter.h"
#include"datatype_rewriter.h"
#include"array_rewriter.h"
#include"fpa_rewriter.h"
#include"rewriter_def.h"
#include"cooperate.h"

struct evaluator_cfg : public default_rewriter_cfg {
    model &                         m_model;
    bool_rewriter                   m_b_rw;
    arith_rewriter                  m_a_rw;
    bv_rewriter                     m_bv_rw;
    array_rewriter                  m_ar_rw;
    datatype_rewriter               m_dt_rw;
    pb_rewriter                     m_pb_rw;
    fpa_rewriter                    m_f_rw;
    unsigned long long              m_max_memory;
    unsigned                        m_max_steps;
    bool                            m_model_completion;
    bool                            m_cache;

    evaluator_cfg(ast_manager & m, model & md, params_ref const & p):
        m_model(md),
        m_b_rw(m),
        // We must allow customers to set parameters for arithmetic rewriter/evaluator. 
        // In particular, the maximum degree of algebraic numbers that will be evaluated.
        m_a_rw(m, p), 
        m_bv_rw(m),
        // See comment above. We want to allow customers to set :sort-store
        m_ar_rw(m, p),
        m_dt_rw(m),
        m_pb_rw(m),
        m_f_rw(m) {
        m_b_rw.set_flat(false);
        m_a_rw.set_flat(false);
        m_bv_rw.set_flat(false);
        m_bv_rw.set_mkbv2num(true);
        updt_params(p);
    }

    void updt_params(params_ref const & _p) {
        model_evaluator_params p(_p);
        m_max_memory       = megabytes_to_bytes(p.max_memory());
        m_max_steps        = p.max_steps();
        m_model_completion = p.completion();
        m_cache            = p.cache();
    }
        
    ast_manager & m() const { return m_model.get_manager(); }

    // Try to use the entries to quickly evaluate the fi
    bool eval_fi(func_interp * fi, unsigned num, expr * const * args, expr_ref & result) {
        if (fi->num_entries() == 0)
            return false; // let get_macro handle it.

        SASSERT(fi->get_arity() == num);

        bool actuals_are_values = true;
    
        for (unsigned i = 0; actuals_are_values && i < num; i++) {
            actuals_are_values = m().is_value(args[i]);
        }
        
        if (!actuals_are_values)
            return false; // let get_macro handle it

        func_entry * entry = fi->get_entry(args);
        if (entry != 0) {
            result = entry->get_result();
            return true;
        }

        return false;
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        family_id fid = f->get_family_id();
        if (fid == null_family_id && num == 0) {
            expr * val = m_model.get_const_interp(f);
            if (val != 0) {
                result = val;
                return BR_DONE;
            }
            
            if (m_model_completion) {
                sort * s   = f->get_range();
                expr * val = m_model.get_some_value(s);
                m_model.register_decl(f, val);
                result = val;
                return BR_DONE;
            }
            return BR_FAILED;
        }

        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m().get_sort(args[0])->get_family_id();
                br_status st = BR_FAILED;
                if (s_fid == m_a_rw.get_fid())
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_a_rw.get_fid())
            return m_a_rw.mk_app_core(f, num, args, result);
        if (fid == m_bv_rw.get_fid())
            return m_bv_rw.mk_app_core(f, num, args, result);
        if (fid == m_ar_rw.get_fid()) 
            return m_ar_rw.mk_app_core(f, num, args, result);
        if (fid == m_dt_rw.get_fid())
            return m_dt_rw.mk_app_core(f, num, args, result);
        if (fid == m_pb_rw.get_fid())
            return m_pb_rw.mk_app_core(f, num, args, result);
        if (fid == m_f_rw.get_fid())
            return m_f_rw.mk_app_core(f, num, args, result);

        func_interp * fi = m_model.get_func_interp(f);
        if (fi != 0 && eval_fi(fi, num, args, result)) {
            TRACE("model_evaluator", tout << "reduce_app " << f->get_name() << "\n";
                  for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
                  tout << "---->\n" << mk_ismt2_pp(result, m()) << "\n";);
            return BR_DONE;
        }
        TRACE("model_evaluator", tout << f->get_name() << "\n";);

        return BR_FAILED;
    }

    bool get_macro(func_decl * f, expr * & def, quantifier * & q, proof * & def_pr) { 

        func_interp * fi = m_model.get_func_interp(f);        
        if (fi != 0) {
            if (fi->is_partial()) {
                if (m_model_completion) {
                    sort * s   = f->get_range();
                    expr * val = m_model.get_some_value(s);
                    fi->set_else(val);
                }
                else {
                    return false;
                }
            }            
            def    = fi->get_interp();
            SASSERT(def != 0);
            return true;
        }

        if (f->get_family_id() == null_family_id && m_model_completion) {
            sort * s   = f->get_range();
            expr * val = m_model.get_some_value(s);
            func_interp * new_fi = alloc(func_interp, m(), f->get_arity());
            new_fi->set_else(val);
            m_model.register_decl(f, new_fi);
            def = val;
            return true;
        }
        return false;
    }

    
    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("model evaluator");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    bool cache_results() const { return m_cache; }

};

template class rewriter_tpl<evaluator_cfg>;

struct model_evaluator::imp : public rewriter_tpl<evaluator_cfg> {
    evaluator_cfg m_cfg;
    imp(model & md, params_ref const & p):
        rewriter_tpl<evaluator_cfg>(md.get_manager(), 
                                    false, // no proofs for evaluator
                                    m_cfg),
        m_cfg(md.get_manager(), md, p) {
    }
};

model_evaluator::model_evaluator(model & md, params_ref const & p) {
    m_imp = alloc(imp, md, p);
}

ast_manager & model_evaluator::m() const {
    return m_imp->m();
}

model_evaluator::~model_evaluator() {
    dealloc(m_imp);
}

void model_evaluator::updt_params(params_ref const & p) {
    m_imp->cfg().updt_params(p);
}

void model_evaluator::get_param_descrs(param_descrs & r) {
    model_evaluator_params::collect_param_descrs(r);
}

void model_evaluator::set_model_completion(bool f) {
    m_imp->cfg().m_model_completion = f;
}

unsigned model_evaluator::get_num_steps() const {
    return m_imp->get_num_steps();
}

void model_evaluator::set_cancel(bool f) {
    #pragma omp critical (model_evaluator)
    {
        m_imp->set_cancel(f);
    }
}

void model_evaluator::cleanup(params_ref const & p) {
    model & md = m_imp->cfg().m_model;
    #pragma omp critical (model_evaluator)
    {
        dealloc(m_imp);
        m_imp = alloc(imp, md, p);
    }
}

void model_evaluator::reset(params_ref const & p) {
    m_imp->reset();
    updt_params(p);
}

void model_evaluator::operator()(expr * t, expr_ref & result) {
    TRACE("model_evaluator", tout << mk_ismt2_pp(t, m()) << "\n";);
    m_imp->operator()(t, result);
}



