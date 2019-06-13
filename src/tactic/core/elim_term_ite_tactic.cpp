/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_term_ite_tactic.cpp

Abstract:

    Eliminate term if-then-else by adding 
    new fresh auxiliary variables.

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/normal_forms/defined_names.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/generic_model_converter.h"

class elim_term_ite_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &               m;
        defined_names               m_defined_names;
        ref<generic_model_converter> m_mc;
        goal *                      m_goal;
        unsigned long long          m_max_memory; // in bytes
        bool                        m_produce_models;
        unsigned                    m_num_fresh;

        bool max_steps_exceeded(unsigned num_steps) const { 
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
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
                m_goal->assert_expr(new_def, new_def_pr, nullptr);
                m_num_fresh++;
                if (m_produce_models) {
                    if (!m_mc)
                        m_mc = alloc(generic_model_converter, m, "elim_term_ite");
                    m_mc->hide(_result->get_decl());
                }
            }
            result = _result.get();
            return BR_DONE;
        }
        
        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m),
            m_defined_names(m, nullptr /* don't use prefix */) {
            updt_params(p);
            m_goal      = nullptr;
            m_num_fresh = 0;
        }

        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        }
    };
    
    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;
        
        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    struct imp {
        ast_manager & m;
        rw            m_rw;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_rw(m, p) {
        }
        
        
        void updt_params(params_ref const & p) {
            m_rw.cfg().updt_params(p);
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            tactic_report report("elim-term-ite", *g);
            bool produce_proofs = g->proofs_enabled();
            m_rw.cfg().m_produce_models = g->models_enabled();

            m_rw.m_cfg.m_num_fresh = 0;
            m_rw.m_cfg.m_goal = g.get();
            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned   size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            g->add(m_rw.m_cfg.m_mc.get());
            report_tactic_progress(":elim-term-ite-consts", m_rw.m_cfg.m_num_fresh);
            g->inc_depth();
            result.push_back(g.get());
            TRACE("elim_term_ite", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    elim_term_ite_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }
        
    ~elim_term_ite_tactic() override {
        dealloc(m_imp);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(elim_term_ite_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->m_rw.cfg().updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("max_args", CPK_UINT, 
                 "(default: 128) maximum number of arguments (per application) that will be considered by the greedy (quadratic) heuristic.");
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m;
        m_imp->~imp();
        m_imp = new (m_imp) imp(m, m_params);
    }

};

tactic * mk_elim_term_ite_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(elim_term_ite_tactic, m, p));
}
