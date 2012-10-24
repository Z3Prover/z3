/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_tactic.cpp

Abstract:

    General purpose tactic for UFBV benchmarks.

Author:

    Christoph (cwinter) 2012-10-24

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"nnf.h"
#include"solve_eqs_tactic.h"
#include"simplifier.h"
#include"basic_simplifier_plugin.h"
#include"arith_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"macro_manager.h"
#include"macro_finder.h"
#include"elim_var_model_converter.h"
#include"ufbv_rewriter.h"
#include"distribute_forall_tactic.h"
#include"der.h"
#include"smt_tactic.h"
#include"ufbv_tactic.h"

class macro_finder_tactic : public tactic {    

    struct imp {
        ast_manager & m_manager;
        bool m_cancel;
        bool m_elim_and;

        imp(ast_manager & m, params_ref const & p) : m_manager(m),m_elim_and(false),m_cancel(false) {
            updt_params(p);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("macro-finder", *g);
            fail_if_unsat_core_generation("macro-finder", g);

            bool produce_proofs = g->proofs_enabled();
            bool produce_models = g->models_enabled();

            simplifier simp(m_manager);
            basic_simplifier_plugin * bsimp = alloc(basic_simplifier_plugin, m_manager);
            bsimp->set_eliminate_and(m_elim_and);
            simp.register_plugin(bsimp);
            arith_simplifier_params a_params;
            arith_simplifier_plugin * asimp = alloc(arith_simplifier_plugin, m_manager, *bsimp, a_params);
            simp.register_plugin(asimp);
            bv_simplifier_params bv_params;
            bv_simplifier_plugin * bvsimp = alloc(bv_simplifier_plugin, m_manager, *bsimp, bv_params);
            simp.register_plugin(bvsimp);
                
            macro_manager mm(m_manager, simp);
            macro_finder mf(m_manager, mm);
            
            expr_ref_vector forms(m_manager), new_forms(m_manager);
            proof_ref_vector proofs(m_manager), new_proofs(m_manager);            
            unsigned   size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                forms.push_back(g->form(idx));
                proofs.push_back(g->pr(idx));                
            }

            mf(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);
        
            unsigned i = 0;
            for (; i < g->size(); i++)
                g->update(i, new_forms.get(i), produce_proofs ? new_proofs.get(i) : 0, g->dep(i));

            for (; i < new_forms.size(); i++)
                g->assert_expr(new_forms.get(i), new_proofs.get(i), 0);

            elim_var_model_converter * evmc = alloc(elim_var_model_converter, mm.get_manager());
            unsigned num = mm.get_num_macros();
            for (unsigned i = 0; i < num; i++) {
                expr_ref f_interp(mm.get_manager());
                func_decl * f = mm.get_macro_interpretation(i, f_interp);
                evmc->insert(f, f_interp);
            }
            mc = evmc;
                        
            g->inc_depth();
            result.push_back(g.get());
            TRACE("macro-finder", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
            m_elim_and = p.get_bool(":elim-and", false);
        }
    };

    imp *      m_imp;
    params_ref m_params;    
public:
    macro_finder_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(macro_finder_tactic, m, m_params);
    }
        
    virtual ~macro_finder_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
        r.insert(":elim-and", CPK_BOOL, "(default: false) eliminate conjunctions during (internal) calls to the simplifier.");
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_macro_finder_tactic(ast_manager & m, params_ref const & p) {
    return alloc(macro_finder_tactic, m, p);
}

class ufbv_rewriter_tactic : public tactic {

    struct imp {
        ast_manager & m_manager;
        bool m_cancel;

        imp(ast_manager & m, params_ref const & p) : m_manager(m),m_cancel(false) {
            updt_params(p);
        }
        
        ast_manager & m() const { return m_manager; }
        
        void set_cancel(bool f) {
            m_cancel = f;
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            tactic_report report("ufbv-rewriter", *g);
            fail_if_unsat_core_generation("ufbv-rewriter", g);

            bool produce_proofs = g->proofs_enabled();
            bool produce_models = g->models_enabled();
            
            basic_simplifier_plugin bsimp(m_manager);
            bsimp.set_eliminate_and(true);
            ufbv_rewriter dem(m_manager, bsimp);
            
            expr_ref_vector forms(m_manager), new_forms(m_manager);
            proof_ref_vector proofs(m_manager), new_proofs(m_manager);

            unsigned size = g->size();
            for (unsigned i = 0; i < size; i++) {
                forms.push_back(g->form(i));
                proofs.push_back(g->pr(i));
            }

            dem(forms.size(), forms.c_ptr(), proofs.c_ptr(), new_forms, new_proofs);
        
            unsigned i = 0;
            for (; i < g->size(); i++)
                g->update(i, new_forms.get(i), produce_proofs ? new_proofs.get(i) : 0, g->dep(i));

            for (; i < new_forms.size(); i++)
                g->assert_expr(new_forms.get(i), new_proofs.get(i), 0);

            mc = 0; // CMW: Remark: The demodulator could potentially remove all references to a variable. 

            g->inc_depth();
            result.push_back(g.get());
            TRACE("ufbv-rewriter", g->display(tout););
            SASSERT(g->is_well_sorted());
        }

        void updt_params(params_ref const & p) {
        }
    };
    
    imp *      m_imp;
    params_ref m_params;

public:
    ufbv_rewriter_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(ufbv_rewriter_tactic, m, m_params);
    }
        
    virtual ~ufbv_rewriter_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
        insert_max_memory(r);
        insert_produce_models(r);
        insert_produce_proofs(r);
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m();
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_ufbv_rewriter_tactic(ast_manager & m, params_ref const & p) {
    return alloc(ufbv_rewriter_tactic, m, p);
}

tactic * mk_der_fp(ast_manager & m, params_ref const & p) {
    return repeat(and_then(mk_der_tactic(m), mk_simplify_tactic(m, p)));
}

tactic * mk_ufbv_preprocessor_tactic(ast_manager & m, params_ref const & p) {
    params_ref elim_and_p;
    elim_and_p.set_bool(":elim-and", true);

    return and_then(
                and_then(mk_simplify_tactic(m, p),
                         mk_propagate_values_tactic(m, p),
                         and_then(mk_macro_finder_tactic(m, elim_and_p),
                         mk_macro_finder_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_snf_tactic(m, p), mk_simplify_tactic(m, p)),
                         mk_simplify_tactic(m, elim_and_p),
                         mk_solve_eqs_tactic(m, p),
                         and_then(mk_der_fp(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_distribute_forall_tactic(m, p), mk_simplify_tactic(m, p))),
                and_then( // and_then(mk_reduce_args(m, p), mk_simplify_tactic(m, p)),
                          and_then(mk_macro_finder_tactic(m, elim_and_p), mk_simplify_tactic(m, p)),
                          and_then(mk_ufbv_rewriter_tactic(m, p), mk_simplify_tactic(m, p)),
                          // and_then(mk_quasi_macros(m, p), mk_simplify_tactic(m, p)),
                          and_then(mk_der_fp(m, p), mk_simplify_tactic(m, p)),
                          mk_simplify_tactic(m, p)));
}

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p(p);    
    main_p.set_bool(":mbqi", true);
    main_p.set_uint(":mbqi-max-iterations", -1);
    main_p.set_bool(":elim-and", true);
    main_p.set_bool(":solver", true);

    params_ref smt_p(p);
    smt_p.set_bool(":auto-config", false);

    tactic * t = and_then(repeat(mk_ufbv_preprocessor_tactic(m, main_p), 2),
                          using_params(mk_smt_tactic(smt_p), main_p));
    
    t->updt_params(p);

    return t;
}