/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_prover.cpp

Abstract:

    Stand-alone SPC prover (it is mainly for debugging purposes).

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#include"spc_prover.h"
#include"spc_decl_plugin.h"
#include"for_each_expr.h"

namespace spc {
    prover::prover(ast_manager & m, front_end_params & params):
        m_manager(m),
        m_params(params),
        m_simplifier(m),
        m_defined_names(m),
        m_preprocessor(m, m_defined_names, m_simplifier, params),
        m_order(0),
        m_cls_sel(0),
        m_lit_sel(0),
        m_context(0),
        m_exprs(m),
        m_expr_proofs(m),
        m_has_theories(false) {

        family_id fid = m_manager.get_family_id("spc");
        if (!m_manager.has_plugin(fid)) 
            m_manager.register_plugin(fid, alloc(spc_decl_plugin));

        // This piece of code shows why the old model for passing parameters is broken.
        // spc::prover must overwrite some parameters, but this modification affects other
        // components. :-( 
        // TODO: move everything to the new params_ref object
        params.m_nnf_mode = NNF_FULL;
        params.m_cnf_mode = CNF_FULL;
        params.m_lift_ite = LI_CONSERVATIVE;

        basic_simplifier_plugin * basic = alloc(basic_simplifier_plugin, m_manager);
        m_simplifier.register_plugin(basic);
        m_simplifier.register_plugin(alloc(arith_simplifier_plugin, m_manager, *basic, params));
    }

    prover::~prover() {
        if (m_context) {
            dealloc(m_context);
            dealloc(m_lit_sel);
            dealloc(m_cls_sel);
            dealloc(m_order);
        }
    }

    void prover::init() {
        if (m_context)
            return;
        precedence * p = mk_precedence(m_manager, m_params);

        // TODO use params to configure the following functors.
        m_order    = alloc(kbo, m_manager, p); 
        
        clause_eval * evals[2]  = { alloc(symbol_count_clause_eval), alloc(time_clause_eval) };
        unsigned      slots[2] = { 10, 1 };
        m_cls_sel  = alloc(clause_selection, 2, evals, slots);
        
        m_lit_sel  = alloc(max_no_selection, *m_order);
        // m_lit_sel  = new complex_literal_selection(m_manager);
        // m_lit_sel  = new diff_literal_selection(m_manager);
        // m_lit_sel  = new no_literal_selection(); // new diff_literal_selection(m_manager);
        // END TODO
        
        m_context  = alloc(context, m_manager, *m_order, *m_cls_sel, *m_lit_sel, m_simplifier, m_params);
    }

    struct has_theories_proc {
        ast_manager & m_manager;
        has_theories_proc(ast_manager & m):m_manager(m) {}
        struct found {}; 
        void operator()(var * n) {}
        void operator()(app * n) { if (!m_manager.is_builtin_family_id(n->get_family_id())) throw found(); }
        void operator()(quantifier * n) {}
    };

    bool has_theories(ast_manager & m, expr * e) {
        has_theories_proc p(m);
        try {
            for_each_expr(p, e);
        }
        catch (has_theories_proc::found) {
            return true;
        }
        return false;
    }
        
    void prover::assert_expr(expr * e) {
        if (!m_has_theories && has_theories(m_manager, e))
            m_has_theories = true;
        TRACE("spc_assert", tout << mk_pp(e, m_manager) << "\nhas_theories: " << m_has_theories << "\n";);
        m_preprocessor(e, m_manager.mk_asserted(e), m_exprs, m_expr_proofs);
    }

    lbool prover::check() {
        init();
        unsigned sz = m_exprs.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * curr = m_exprs.get(i);
            proof * p   = m_manager.proofs_enabled() ? m_expr_proofs.get(i) : m_manager.mk_undef_proof();
            m_context->assert_expr(curr, p);
        }
        m_exprs.reset();
        m_expr_proofs.reset();

        m_context->saturate(m_params.m_spc_num_iterations);
        if (m_context->inconsistent())
            return l_false;
        else if (m_context->processed_all())
            return m_has_theories ? l_undef : l_true;
        else
            return l_undef;
    }
};

