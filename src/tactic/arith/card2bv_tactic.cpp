/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

Notes:

--*/
#include "tactic/tactical.h"
#include "ast/ast_smt2_pp.h"
#include "tactic/arith/card2bv_tactic.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "tactic/generic_model_converter.h"

class card2bv_tactic : public tactic {
    ast_manager &              m;
    params_ref                 m_params;
    
public:

    card2bv_tactic(ast_manager & m, params_ref const & p):
        m(m),
        m_params(p) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(card2bv_tactic, m, m_params);
    }

    ~card2bv_tactic() override {
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
    }

    void collect_param_descrs(param_descrs & r) override {  
        r.insert("keep_cardinality_constraints", CPK_BOOL, "(default: true) retain cardinality constraints for solver");        
    }

    
    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        TRACE("card2bv-before", g->display(tout););
        SASSERT(g->is_well_sorted());
        result.reset();
        tactic_report report("card2bv", *g);
        th_rewriter rw1(m, m_params);
        pb2bv_rewriter rw2(m, m_params);
        
        if (g->inconsistent()) {
            result.push_back(g.get());
            return;
        }
                
        expr_ref new_f1(m), new_f2(m);
        proof_ref new_pr1(m), new_pr2(m);
        for (unsigned idx = 0; !g->inconsistent() && idx < g->size(); idx++) {
            rw1(g->form(idx), new_f1, new_pr1);
            TRACE("card2bv", tout << "Rewriting " << mk_ismt2_pp(new_f1.get(), m) << std::endl;);
            rw2(false, new_f1, new_f2, new_pr2);
            if (m.proofs_enabled()) {
                new_pr1  = m.mk_modus_ponens(g->pr(idx), new_pr1);
                new_pr1  = m.mk_modus_ponens(new_pr1, new_pr2);
            }
            g->update(idx, new_f2, new_pr1, g->dep(idx));
        }
        expr_ref_vector fmls(m);
        rw2.flush_side_constraints(fmls);
        for (expr* e : fmls) {
            g->assert_expr(e);
        }

        func_decl_ref_vector const& fns = rw2.fresh_constants();
        if (!fns.empty()) {
            generic_model_converter* filter = alloc(generic_model_converter, m, "card2bv");
            for (func_decl* f : fns) filter->hide(f);
            g->add(filter);
        }

        g->inc_depth();
        result.push_back(g.get());
        TRACE("card2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    void cleanup() override {
    }
};

tactic * mk_card2bv_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(card2bv_tactic, m, p));
}

