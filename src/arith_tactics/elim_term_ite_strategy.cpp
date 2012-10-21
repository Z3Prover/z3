/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_term_ite_strategy.cpp

Abstract:

    Eliminate term if-then-else by adding 
    new fresh auxiliary variables.

Author:

    Leonardo (leonardo) 2011-06-15

Notes:

--*/
#include"elim_term_ite_strategy.h"
#include"defined_names.h"
#include"rewriter_def.h"
#include"filter_model_converter.h"
#include"cooperate.h"

struct elim_term_ite_strategy::imp {
    
    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &               m;
        defined_names               m_defined_names;
        ref<filter_model_converter> m_mc;
        assertion_set *             m_set;
        unsigned long long          m_max_memory; // in bytes
        bool                        m_produce_models;
        unsigned                    m_num_fresh;

        bool max_steps_exceeded(unsigned num_steps) const { 
            cooperate("elim term ite");
            if (memory::get_allocation_size() > m_max_memory)
                throw elim_term_ite_exception(STE_MAX_MEMORY_MSG);
            return false;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if (!m.is_term_ite(f))
                return BR_FAILED;
            expr_ref new_ite(m);
            new_ite = m.mk_app(f, num, args);
            
            expr_ref new_def(m);
            proof_ref new_def_pr(m);
            app_ref _result(m);
            if (m_defined_names.mk_name(new_ite, new_def, new_def_pr, _result, result_pr)) {
                m_set->assert_expr(new_def, new_def_pr);
                m_num_fresh++;
                if (m_produce_models) {
                    if (!m_mc)
                        m_mc = alloc(filter_model_converter, m);
                    m_mc->insert(_result->get_decl());
                }
            }
            result = _result.get();
            return BR_DONE;
        }
        
        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m),
            m_defined_names(m, 0 /* don't use prefix */) {
            updt_params(p);
            m_set       = 0;
            m_num_fresh = 0;
        }

        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint(":max-memory", UINT_MAX));
            m_produce_models = p.get_bool(":produce-models", false);
        }
    };
    
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        
        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    ast_manager & m;
    rw            m_rw;

    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_rw(m, p) {
    }

    void set_cancel(bool f) {
        m_rw.set_cancel(f);
    }

    void updt_params(params_ref const & p) {
        m_rw.cfg().updt_params(p);
    }
    
    void operator()(assertion_set & s, model_converter_ref & mc) {
        mc = 0;
        if (s.inconsistent()) 
            return;
        {
            as_st_report report("elim-term-ite", s);
            m_rw.m_cfg.m_num_fresh = 0;
            m_rw.m_cfg.m_set = &s;
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned   size = s.size();
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = s.form(idx);
                m_rw(curr, new_curr, new_pr);
                if (m.proofs_enabled()) {
                    proof * pr = s.pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                s.update(idx, new_curr, new_pr);
            }
            mc = m_rw.m_cfg.m_mc.get();
        }
        report_st_progress(":elim-term-ite-consts", m_rw.m_cfg.m_num_fresh);
    }
};


elim_term_ite_strategy::elim_term_ite_strategy(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

elim_term_ite_strategy::~elim_term_ite_strategy() {
    dealloc(m_imp);
}

void elim_term_ite_strategy::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->updt_params(p);
}

void elim_term_ite_strategy::get_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    insert_produce_models(r);
}

void elim_term_ite_strategy::operator()(assertion_set & s, model_converter_ref & mc) {
    m_imp->operator()(s, mc);
}

void elim_term_ite_strategy::set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}
 
void elim_term_ite_strategy::cleanup() {
    ast_manager & m = m_imp->m;
    imp * d = m_imp;
    #pragma omp critical (as_st_cancel)
    {
        d = m_imp;
    }
    dealloc(d);
    d = alloc(imp, m, m_params);
    #pragma omp critical (as_st_cancel) 
    {
        m_imp = d;
    }
}

