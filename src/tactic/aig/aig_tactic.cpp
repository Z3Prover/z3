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
#include "ast/ast_util.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_expr.h"
#include "tactic/tactical.h"
#include "tactic/aig/aig.h"

class aig_manager;

class aig_tactic : public tactic {
    unsigned long long m_max_memory;
    bool               m_aig_gate_encoding;
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

    char const* name() const override { return "aig"; }
    
    tactic * translate(ast_manager & m) override {
        aig_tactic * t = alloc(aig_tactic);
        t->m_max_memory = m_max_memory;
        t->m_aig_gate_encoding = m_aig_gate_encoding;
        return t;
    }

    void updt_params(params_ref const & p) override {
        m_max_memory        = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_aig_gate_encoding = p.get_bool("aig_default_gate_encoding", true);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
    }

    void operator()(goal_ref const & g) {
        ast_manager& m = g->m();
        mk_aig_manager mk(*this, m);

        expr_ref_vector nodeps(m);
        
        for (unsigned i = 0; i < g->size(); i++) {
            expr_dependency * ed = g->dep(i);
            if (!ed) {
                nodeps.push_back(g->form(i));
                g->update(i, m.mk_true());
            }
            else {
                aig_ref r = m_aig_manager->mk_aig(g->form(i));
                m_aig_manager->max_sharing(r);
                expr_ref new_f(m);
                m_aig_manager->to_formula(r, new_f);
                unsigned old_sz = get_num_exprs(g->form(i));
                unsigned new_sz = get_num_exprs(new_f);
                if (new_sz <= 1.2*old_sz)
                    g->update(i, new_f, nullptr, ed);
            }
        }

        if (!nodeps.empty()) {
            expr_ref conj(::mk_and(nodeps));
            aig_ref r = m_aig_manager->mk_aig(conj);
            m_aig_manager->max_sharing(r);
            expr_ref new_f(m);
            m_aig_manager->to_formula(r, new_f);
            unsigned old_sz = get_num_exprs(conj);
            unsigned new_sz = get_num_exprs(new_f);
            
            if (new_sz > 1.2*old_sz)
                new_f = conj;
            g->assert_expr(new_f);                       
        }
        g->elim_true();
    }
    
    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        fail_if_proof_generation("aig", g);
        tactic_report report("aig", *g);
        operator()(g);
        g->inc_depth();
        result.push_back(g.get());
    }

    void cleanup() override {}

};

tactic * mk_aig_tactic(params_ref const & p) {
    return clean(alloc(aig_tactic, p));
}
