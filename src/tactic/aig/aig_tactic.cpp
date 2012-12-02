/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    aig_tactic.cpp

Abstract:

    Tactic for minimizing circuits using AIGs.

Author:

    Leonardo (leonardo) 2011-10-24

Notes:

--*/
#include"tactical.h"
#include"aig.h"

class aig_manager;

class aig_tactic : public tactic {
    unsigned long long m_max_memory;
    bool               m_aig_gate_encoding;
    bool               m_aig_per_assertion;
    aig_manager *      m_aig_manager;

    struct mk_aig_manager {
        aig_tactic & m_owner;

        mk_aig_manager(aig_tactic & o, ast_manager & m):m_owner(o) {
            aig_manager * mng = alloc(aig_manager, m, o.m_max_memory, o.m_aig_gate_encoding);
            #pragma omp critical (aig_tactic)
            {
                m_owner.m_aig_manager = mng;
            }
        }
        
        ~mk_aig_manager() {
            aig_manager * mng = m_owner.m_aig_manager;
            #pragma omp critical (aig_tactic)
            {
                m_owner.m_aig_manager = 0;
            }
            dealloc(mng);
        }
    };

public:
    aig_tactic(params_ref const & p = params_ref()):m_aig_manager(0) { 
        updt_params(p); 
    }
    
    virtual tactic * translate(ast_manager & m) {
        aig_tactic * t = alloc(aig_tactic);
        t->m_max_memory = m_max_memory;
        t->m_aig_gate_encoding = m_aig_gate_encoding;
        t->m_aig_per_assertion = m_aig_per_assertion;
        return t;
    }

    virtual void updt_params(params_ref const & p) {
        m_max_memory        = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_aig_gate_encoding = p.get_bool("aig_default_gate_encoding", true);
        m_aig_per_assertion = p.get_bool("aig_per_assertion", true); 
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        insert_max_memory(r);
        r.insert("aig_per_assertion", CPK_BOOL, "(default: true) process one assertion at a time.");
    }

    void operator()(goal_ref const & g) {
        SASSERT(g->is_well_sorted());
        tactic_report report("aig", *g);

        mk_aig_manager mk(*this, g->m());
        if (m_aig_per_assertion) {
            unsigned size = g->size();
            for (unsigned i = 0; i < size; i++) {
                aig_ref r = m_aig_manager->mk_aig(g->form(i));
                m_aig_manager->max_sharing(r);
                expr_ref new_f(g->m());
                m_aig_manager->to_formula(r, new_f);
                g->update(i, new_f, 0, g->dep(i));
            }
        }
        else {
            fail_if_unsat_core_generation("aig", g);
            aig_ref r = m_aig_manager->mk_aig(*(g.get()));
            g->reset(); // save memory
            m_aig_manager->max_sharing(r);
            m_aig_manager->to_formula(r, *(g.get()));
        }
        SASSERT(g->is_well_sorted());
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        fail_if_proof_generation("aig", g);
        mc = 0; pc = 0; core = 0;
        operator()(g);
        g->inc_depth();
        result.push_back(g.get());
    }

    virtual void cleanup() {}

protected:
    virtual void set_cancel(bool f) {
        #pragma omp critical (aig_tactic)
        {
            if (m_aig_manager)
                m_aig_manager->set_cancel(f);
        }
    }
};

tactic * mk_aig_tactic(params_ref const & p) {
    return clean(alloc(aig_tactic, p));
}
