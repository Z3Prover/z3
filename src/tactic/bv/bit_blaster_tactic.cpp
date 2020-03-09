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
#include "tactic/tactical.h"
#include "tactic/bv/bit_blaster_model_converter.h"
#include "ast/rewriter/bit_blaster/bit_blaster_rewriter.h"
#include "ast/ast_pp.h"
#include "model/model_pp.h"
#include "ast/rewriter/rewriter_types.h"

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
                        goal_ref_buffer & result) {
            bool proofs_enabled = g->proofs_enabled();

            if (proofs_enabled && m_blast_quant)
                throw tactic_exception("quantified variable blasting does not support proof generation");
            
            tactic_report report("bit-blast", *g);
            
            TRACE("before_bit_blaster", g->display(tout););
            m_num_steps = 0;
            
            m_rewriter->start_rewrite();
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
                    TRACE("bit_blaster", tout << mk_pp(curr, m()) << " -> " << new_curr << "\n";);
                    g->update(idx, new_curr, new_pr, g->dep(idx));
                }
            }
            
            if (change && g->models_enabled()) {
                obj_map<func_decl, expr*> const2bits;
                ptr_vector<func_decl> newbits;
                m_rewriter->end_rewrite(const2bits, newbits);
                g->add(mk_bit_blaster_model_converter(m(), const2bits, newbits));
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("after_bit_blaster", g->display(tout); if (g->mc()) g->mc()->display(tout); tout << "\n";);
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

    tactic * translate(ast_manager & m) override {
        SASSERT(!m_rewriter); // assume translation isn't used where rewriter is external.
        return alloc(bit_blaster_tactic, m, nullptr, m_params);
    }

    ~bit_blaster_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("blast_mul", CPK_BOOL, "(default: true) bit-blast multipliers (and dividers, remainders).");
        r.insert("blast_add", CPK_BOOL, "(default: true) bit-blast adders.");
        r.insert("blast_quant", CPK_BOOL, "(default: false) bit-blast quantified variables.");
        r.insert("blast_full", CPK_BOOL, "(default: false) bit-blast any term with bit-vector sort, this option will make E-matching ineffective in any pattern containing bit-vector terms.");
    }
     
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        try {
            (*m_imp)(g, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }

    void cleanup() override {
        imp * d = alloc(imp, m_imp->m(), m_rewriter, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
    
    unsigned get_num_steps() const {
        return m_imp->get_num_steps();
    }


};


tactic * mk_bit_blaster_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bit_blaster_tactic, m, nullptr, p));
}

tactic * mk_bit_blaster_tactic(ast_manager & m, bit_blaster_rewriter* rw, params_ref const & p) {
    return clean(alloc(bit_blaster_tactic, m, rw, p));
}

