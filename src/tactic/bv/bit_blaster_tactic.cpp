/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_tactic.cpp

Abstract:

    Apply bit-blasting to a given goal

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#include"tactical.h"
#include"bit_blaster_model_converter.h"
#include"bit_blaster_rewriter.h"
#include"ast_pp.h"
#include"model_pp.h"
#include"rewriter_types.h"

class bit_blaster_tactic : public tactic {


    struct imp {
        bit_blaster_rewriter   m_base_rewriter;
        bit_blaster_rewriter*  m_rewriter;    
        unsigned               m_num_steps;
        bool                   m_blast_quant;

        imp(ast_manager & m, bit_blaster_rewriter* rw, params_ref const & p):
            m_base_rewriter(m, p),
            m_rewriter(rw?rw:&m_base_rewriter) {
            updt_params(p);
        }

        void updt_params_core(params_ref const & p) {
            m_blast_quant = p.get_bool("blast_quant", false);
        }

        void updt_params(params_ref const & p) {
            m_rewriter->updt_params(p);
            updt_params_core(p);
        }
        
        ast_manager & m() const { return m_rewriter->m(); }
        

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            mc = 0; pc = 0; core = 0;
            bool proofs_enabled = g->proofs_enabled();

            if (proofs_enabled && m_blast_quant)
                throw tactic_exception("quantified variable blasting does not support proof generation");
            
            tactic_report report("bit-blaster", *g);
            
            TRACE("before_bit_blaster", g->display(tout););
            m_num_steps = 0;
            
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            unsigned size = g->size();
            bool change = false;
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                (*m_rewriter)(curr, new_curr, new_pr);
                m_num_steps += m_rewriter->get_num_steps();
                if (proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr     = m().mk_modus_ponens(pr, new_pr);
                }
                if (curr != new_curr) {
                    change = true;
                    TRACE("bit_blaster", tout << mk_pp(curr, m()) << " -> " << mk_pp(new_curr, m()) << "\n";);
                    g->update(idx, new_curr, new_pr, g->dep(idx));
                }
            }
            
            if (change && g->models_enabled())  
                mc = mk_bit_blaster_model_converter(m(), m_rewriter->const2bits());
            else
                mc = 0;
            g->inc_depth();
            result.push_back(g.get());
            TRACE("after_bit_blaster", g->display(tout); if (mc) mc->display(tout); tout << "\n";);
            m_rewriter->cleanup();
        }
        
        unsigned get_num_steps() const { return m_num_steps; }
    };

    imp *      m_imp;
    bit_blaster_rewriter* m_rewriter;
    params_ref m_params;

public:
    bit_blaster_tactic(ast_manager & m, bit_blaster_rewriter* rw, params_ref const & p):
        m_rewriter(rw),
        m_params(p) {
        m_imp = alloc(imp, m, m_rewriter, p);
    }

    virtual tactic * translate(ast_manager & m) {
        SASSERT(!m_rewriter); // assume translation isn't used where rewriter is external.
        return alloc(bit_blaster_tactic, m, 0, m_params); 
    }

    virtual ~bit_blaster_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("blast_mul", CPK_BOOL, "(default: true) bit-blast multipliers (and dividers, remainders).");
        r.insert("blast_add", CPK_BOOL, "(default: true) bit-blast adders.");
        r.insert("blast_quant", CPK_BOOL, "(default: false) bit-blast quantified variables.");
        r.insert("blast_full", CPK_BOOL, "(default: false) bit-blast any term with bit-vector sort, this option will make E-matching ineffective in any pattern containing bit-vector terms.");
    }
     
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            (*m_imp)(g, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    virtual void cleanup() {
        imp * d = alloc(imp, m_imp->m(), m_rewriter, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
    
    unsigned get_num_steps() const {
        return m_imp->get_num_steps();
    }

};


tactic * mk_bit_blaster_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bit_blaster_tactic, m, 0, p));
}

tactic * mk_bit_blaster_tactic(ast_manager & m, bit_blaster_rewriter* rw, params_ref const & p) {
    return clean(alloc(bit_blaster_tactic, m, rw, p));
}
