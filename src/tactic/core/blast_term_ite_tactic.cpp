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
#include"tactical.h"
#include"defined_names.h"
#include"rewriter_def.h"
#include"filter_model_converter.h"
#include"cooperate.h"
#include"scoped_proof.h"



// 
// (f (if c1 (if c2 e1 e2) e3) b c) -> 
// (if c1 (if c2 (f e1 b c)
//


class blast_term_ite_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager& m;
        unsigned long long          m_max_memory; // in bytes
        unsigned m_num_fresh; // number of expansions

        rw_cfg(ast_manager & _m, params_ref const & p):
            m(_m),
            m_num_fresh(0) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        }

        bool max_steps_exceeded(unsigned num_steps) const { 
            cooperate("blast term ite");
            // if (memory::get_allocation_size() > m_max_memory) 
            //    throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            return false;
        }
        
        br_status mk_app_core(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result) {
            if (m.is_ite(f)) {
                return BR_FAILED;
            }
            for (unsigned i = 0; i < num_args; ++i) {
                expr* c, *t, *e;
                if (!m.is_bool(args[i]) && m.is_ite(args[i], c, t, e)) {
                    enable_trace("blast_term_ite");
                    TRACE("blast_term_ite", result = m.mk_app(f, num_args, args); tout << result << "\n";);
                    expr_ref e1(m), e2(m);
                    ptr_vector<expr> args1(num_args, args);
                    args1[i] = t;
                    ++m_num_fresh;
                    e1 = m.mk_app(f, num_args, args1.c_ptr());
                    if (t == e) {
                        result = e1;
                        return BR_REWRITE1;
                    }
                    args1[i] = e;
                    e2 = m.mk_app(f, num_args, args1.c_ptr());
                    result = m.mk_app(f, num_args, args);
                    result = m.mk_ite(c, e1, e2);
                    return BR_REWRITE3;
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
            m_rw.cfg().updt_params(p);
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("blast-term-ite", *g);
            bool produce_proofs = g->proofs_enabled();

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
            report_tactic_progress(":blast-term-ite-consts", m_rw.m_cfg.m_num_fresh);
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

    virtual tactic * translate(ast_manager & m) {
        return alloc(blast_term_ite_tactic, m, m_params);
    }
        
    virtual ~blast_term_ite_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("max_args", CPK_UINT, 
                 "(default: 128) maximum number of arguments (per application) that will be considered by the greedy (quadratic) heuristic.");
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        dealloc(m_imp);
        m_imp = alloc(imp, m, m_params);
    }

    static void blast_term_ite(expr_ref& fml) {
        ast_manager& m = fml.get_manager();
        scoped_no_proof _sp(m);
        params_ref p;
        rw ite_rw(m, p);
        expr_ref tmp(m);
        ite_rw(fml, tmp);
        fml = tmp;        
    }
};

tactic * mk_blast_term_ite_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(blast_term_ite_tactic, m, p));
}

void blast_term_ite(expr_ref& fml) {
    blast_term_ite_tactic::blast_term_ite(fml);
}
