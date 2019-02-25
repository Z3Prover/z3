/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    blast_term_ite_tactic.cpp

Abstract:

    Blast term if-then-else by hoisting them up.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-11-4

Notes:

--*/
#include "util/cooperate.h"
#include "ast/normal_forms/defined_names.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/scoped_proof.h"
#include "tactic/tactical.h"
#include "tactic/tactic_params.hpp"



// 
// (f (if c1 (if c2 e1 e2) e3) b c) -> 
// (if c1 (if c2 (f e1 b c)
//


class blast_term_ite_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager&         m;
        unsigned long long   m_max_memory; // in bytes
        unsigned             m_num_fresh; // number of expansions
        unsigned             m_max_steps;
        unsigned             m_max_inflation;
        unsigned             m_init_term_size;

        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m),
            m_num_fresh(0),
            m_max_steps(UINT_MAX), 
            m_max_inflation(UINT_MAX), 
            m_init_term_size(0) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            tactic_params tp(p);
            m_max_memory    = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_max_steps = p.get_uint("max_steps", tp.blast_term_ite_max_steps());
            m_max_inflation = p.get_uint("max_inflation", tp.blast_term_ite_max_inflation());  // multiplicative factor of initial term size.
        }

        

        bool max_steps_exceeded(unsigned num_steps) const { 
            cooperate("blast term ite");
            // if (memory::get_allocation_size() > m_max_memory) 
            //    throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            return num_steps >= m_max_steps;
        }
        
        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            if (m.is_ite(f)) {
                return BR_FAILED;
            }
            if (m_max_inflation < UINT_MAX && 
                m_init_term_size > 0 && 
                m_max_inflation * m_init_term_size < m_num_fresh) 
                return BR_FAILED;
            
            for (unsigned i = 0; i < num_args; ++i) {
                expr* c, *t, *e;
                if (!m.is_bool(args[i]) && m.is_ite(args[i], c, t, e)) {
                    TRACE("blast_term_ite", result = m.mk_app(f, num_args, args); tout << result << "\n";);
                    expr_ref e1(m), e2(m);
                    ptr_vector<expr> args1(num_args, args);
                    args1[i] = t;
                    e1 = m.mk_app(f, num_args, args1.c_ptr());
                    if (m.are_equal(t, e)) {
                        result = e1;
                        return BR_REWRITE1;
                    }
                    else {
                        args1[i] = e;
                        e2 = m.mk_app(f, num_args, args1.c_ptr());
                        result = m.mk_ite(c, e1, e2);
                        ++m_num_fresh;
                        return BR_REWRITE3;
                    }
                }
            }
            return BR_FAILED;
        }

        bool rewrite_patterns() const { return false; }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            return mk_app_core(f, num, args, result);
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
            m_rw.m_cfg.updt_params(p);
        }
        
        void operator()(goal_ref const & g, goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            tactic_report report("blast-term-ite", *g);
            bool produce_proofs = g->proofs_enabled();

            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned   size = g->size();
            unsigned   num_fresh = 0;
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = g->form(idx);
                if (m_rw.m_cfg.m_max_inflation < UINT_MAX) {
                    m_rw.m_cfg.m_init_term_size = get_num_exprs(curr);
                    num_fresh += m_rw.m_cfg.m_num_fresh;
                    m_rw.m_cfg.m_num_fresh = 0;
                }
                m_rw(curr, new_curr, new_pr);
                if (produce_proofs) {
                    proof * pr = g->pr(idx);
                    new_pr     = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            report_tactic_progress(":blast-term-ite-consts", m_rw.m_cfg.m_num_fresh + num_fresh);
            g->inc_depth();
            result.push_back(g.get());
            TRACE("blast_term_ite", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    blast_term_ite_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(blast_term_ite_tactic, m, m_params);
    }
        
    ~blast_term_ite_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->m_rw.m_cfg.updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("max_inflation", CPK_UINT, "(default: infinity) multiplicative factor of initial term size.");
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m;
        dealloc(m_imp);
        m_imp = alloc(imp, m, m_params);
    }

    static void blast_term_ite(expr_ref& fml, unsigned max_inflation) {
        ast_manager& m = fml.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        rw ite_rw(m, p);
        ite_rw.m_cfg.m_max_inflation = max_inflation;
        if (max_inflation < UINT_MAX) {
            ite_rw.m_cfg.m_init_term_size = get_num_exprs(fml);
        }
        try {
            expr_ref tmp(m);
            ite_rw(fml, tmp);
            fml = tmp;   
        }
        catch (z3_exception &) {
            // max steps exceeded.
        }
    }
};

tactic * mk_blast_term_ite_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(blast_term_ite_tactic, m, p));
}

void blast_term_ite(expr_ref& fml, unsigned max_inflation) {
    blast_term_ite_tactic::blast_term_ite(fml, max_inflation);
}
