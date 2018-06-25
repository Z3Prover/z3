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
#include "tactic/tactical.h"
#include "tactic/aig/aig.h"

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
            m_owner.m_aig_manager = mng;            
        }
        
        ~mk_aig_manager() {
            dealloc(m_owner.m_aig_manager);
            m_owner.m_aig_manager = nullptr;
        }
    };

public:
    aig_tactic(params_ref const & p = params_ref()):m_aig_manager(nullptr) {
        updt_params(p); 
    }
    
    tactic * translate(ast_manager & m) override {
        aig_tactic * t = alloc(aig_tactic);
        t->m_max_memory = m_max_memory;
        t->m_aig_gate_encoding = m_aig_gate_encoding;
        t->m_aig_per_assertion = m_aig_per_assertion;
        return t;
    }

    void updt_params(params_ref const & p) override {
        m_max_memory        = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_aig_gate_encoding = p.get_bool("aig_default_gate_encoding", true);
        m_aig_per_assertion = p.get_bool("aig_per_assertion", true); 
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        r.insert("aig_per_assertion", CPK_BOOL, "(default: true) process one assertion at a time.");
    }

    void operator()(goal_ref const & g) {
        SASSERT(g->is_well_sorted());

        mk_aig_manager mk(*this, g->m());
        if (m_aig_per_assertion) {
            for (unsigned i = 0; i < g->size(); i++) {
                aig_ref r = m_aig_manager->mk_aig(g->form(i));
                m_aig_manager->max_sharing(r);
                expr_ref new_f(g->m());
                m_aig_manager->to_formula(r, new_f);
                expr_dependency * ed = g->dep(i);
                g->update(i, new_f, nullptr, ed);
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
    
    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        fail_if_proof_generation("aig", g);
        tactic_report report("aig", *g);
        operator()(g);
        g->inc_depth();
        TRACE("aig", g->display(tout););
        result.push_back(g.get());
    }

    void cleanup() override {}

};

tactic * mk_aig_tactic(params_ref const & p) {
    return clean(alloc(aig_tactic, p));
}
