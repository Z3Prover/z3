/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    nnf_tactic.cpp

Abstract:

    NNF tactic

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#include "ast/normal_forms/nnf.h"
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"

class nnf_tactic : public tactic {
    params_ref    m_params;
    nnf *         m_nnf;

    struct set_nnf {
        nnf_tactic & m_owner;
        
        set_nnf(nnf_tactic & owner, nnf & n):
            m_owner(owner) {
            m_owner.m_nnf = &n;            
        }
        
        ~set_nnf() {
            m_owner.m_nnf = nullptr;
        }
    };
public:
    nnf_tactic(params_ref const & p):
        m_params(p),
        m_nnf(nullptr) {
        TRACE("nnf", tout << "nnf_tactic constructor: " << p << "\n";);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(nnf_tactic, m_params);
    }

    ~nnf_tactic() override {}

    void updt_params(params_ref const & p) override { m_params = p; }

    void collect_param_descrs(param_descrs & r) override { nnf::get_param_descrs(r); }

    void operator()(goal_ref const & g, goal_ref_buffer & result) override {
        TRACE("nnf", tout << "params: " << m_params << "\n"; g->display(tout););
        SASSERT(g->is_well_sorted());
        tactic_report report("nnf", *g);
        bool produce_proofs = g->proofs_enabled();

        ast_manager & m = g->m();
        defined_names dnames(m);
        nnf local_nnf(m, dnames, m_params);
        set_nnf setter(*this, local_nnf);
        
        expr_ref_vector defs(m);
        proof_ref_vector def_prs(m);
        
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        
        unsigned sz = g->size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = g->form(i);
            local_nnf(curr, defs, def_prs, new_curr, new_pr);
            if (produce_proofs) {
                proof * pr = g->pr(i);
                new_pr     = m.mk_modus_ponens(pr, new_pr);
            }
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        
        sz = defs.size();
        for (unsigned i = 0; i < sz; i++) {
            if (produce_proofs)
                g->assert_expr(defs.get(i), def_prs.get(i), nullptr);
            else
                g->assert_expr(defs.get(i), nullptr, nullptr);
        }
        g->inc_depth();
        result.push_back(g.get());
        unsigned num_extra_names = dnames.get_num_names();
        if (num_extra_names > 0) {
            generic_model_converter * fmc = alloc(generic_model_converter, m, "nnf");
            g->add(fmc);
            for (unsigned i = 0; i < num_extra_names; i++)
                fmc->hide(dnames.get_name_decl(i));
        }
        TRACE("nnf", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    void cleanup() override {}
};

tactic * mk_snf_tactic(ast_manager & m, params_ref const & p) {
    return alloc(nnf_tactic, p);
}

tactic * mk_nnf_tactic(ast_manager & m, params_ref const & p) {
    params_ref new_p(p);
    new_p.set_sym("mode", symbol("full"));
    TRACE("nnf", tout << "mk_nnf: " << new_p << "\n";);
    return using_params(mk_snf_tactic(m, p), new_p);
}
