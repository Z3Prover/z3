/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    propagate_values_tactic.cpp

Abstract:

    Propagate values using equalities of the form (= t v) where v is a value,
    and atoms t and (not t)

Author:

    Leonardo de Moura (leonardo) 2011-12-28.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/core/propagate_values_tactic.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/expr_substitution.h"
#include "tactic/goal_shared_occs.h"
#include "params/tactic_params.hpp"

namespace {
class propagate_values_tactic : public tactic {
    ast_manager &                 m;
    th_rewriter                   m_r;
    scoped_ptr<expr_substitution> m_subst;
    goal *                        m_goal;
    goal_shared_occs              m_occs;
    unsigned                      m_idx;
    unsigned                      m_max_rounds;
    bool                          m_modified;
    params_ref                    m_params;

    void updt_params_core(params_ref const & p) {
        tactic_params tp(p);
        m_max_rounds = p.get_uint("max_rounds", tp.propagate_values_max_rounds());
    }

    bool is_shared(expr * t) {
        return m_occs.is_shared(t);
    }

    bool is_shared_neg(expr * t, expr * & atom) {
        if (!m.is_not(t, atom))
            return false;
        return is_shared(atom);
    }

    bool is_shared_eq(expr * t, expr * & lhs, expr * & value, bool& inverted) {
        expr* arg1, *arg2;
        if (!m.is_eq(t, arg1, arg2))
            return false;
        if (m.is_value(arg1) && is_shared(arg2)) {
            lhs   = arg2;
            value = arg1;
            inverted = true;
            return true;
        }
        if (m.is_value(arg2) && is_shared(arg1)) {
            lhs   = arg1;
            value = arg2;
            inverted = false;
            return true;
        }
        return false;
    }

    void push_result(expr * new_curr, proof * new_pr) {
        if (m_goal->proofs_enabled()) {
            proof* pr = m_goal->pr(m_idx);
            new_pr = m.mk_modus_ponens(pr, new_pr);
        }
        else
            new_pr = nullptr;


        expr_dependency_ref new_d(m);
        if (m_goal->unsat_core_enabled()) {
            new_d = m_goal->dep(m_idx);
            expr_dependency * used_d = m_r.get_used_dependencies();
            if (used_d != nullptr) {
                new_d = m.mk_join(new_d, used_d);
                m_r.reset_used_dependencies();
            }
        }
        
        m_goal->update(m_idx, new_curr, new_pr, new_d);

        if (is_shared(new_curr)) {
            m_subst->insert(new_curr, m.mk_true(), m.mk_iff_true(new_pr), new_d);
        }
        expr * atom;
        if (is_shared_neg(new_curr, atom)) {
            m_subst->insert(atom, m.mk_false(), m.mk_iff_false(new_pr), new_d);
        }
        expr * lhs, * value;
        bool inverted = false;
        if (is_shared_eq(new_curr, lhs, value, inverted)) {
            TRACE(shallow_context_simplifier_bug, tout << "found eq:\n" << mk_ismt2_pp(new_curr, m) << "\n" << mk_ismt2_pp(new_pr, m) << "\n";);
            if (inverted && new_pr) new_pr = m.mk_symmetry(new_pr);
            m_subst->insert(lhs, value, new_pr, new_d);
        }
    }

    void process_current() {
        expr * curr = m_goal->form(m_idx);
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        
        if (!m_subst->empty()) {
            m_r(curr, new_curr, new_pr);
        }
        else {
            new_curr = curr;
            if (m.proofs_enabled())
                new_pr   = m.mk_reflexivity(curr);
        }

        TRACE(shallow_context_simplifier_bug, tout << mk_ismt2_pp(curr, m) << "\n---->\n" << new_curr << "\n" << new_pr << "\n";);
        if (new_curr != curr) {
            m_modified = true;
        }
        push_result(new_curr, new_pr);
    }

    void run(goal_ref const & g, goal_ref_buffer & result) {
        tactic_report report("propagate-values", *g);
        m_goal = g.get();

        bool forward   = true;
        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned size  = m_goal->size();
        m_idx          = 0;
        m_modified     = false;
        unsigned round = 0;


        if (m_goal->inconsistent())
            goto end;

        if (m_max_rounds == 0)
            goto end;

        if (m_goal->proofs_enabled())
            goto end;

        m_subst = alloc(expr_substitution, m, g->unsat_core_enabled(), g->proofs_enabled());
        m_r.set_substitution(m_subst.get());
        m_occs(*m_goal);

        while (true) {
            TRACE(propagate_values, tout << "while(true) loop\n"; m_goal->display_with_dependencies(tout););
            if (forward) {
                for (; m_idx < size; m_idx++) {
                    process_current();
                    if (m_goal->inconsistent()) 
                        goto end;
                }
                if (m_subst->empty() && !m_modified)
                    goto end;
                m_occs(*m_goal);
                m_idx        = m_goal->size();
                forward      = false;
                m_subst->reset();
                m_r.set_substitution(m_subst.get()); // reset, but keep substitution
            }
            else {
                while (m_idx > 0) {
                    m_idx--;
                    process_current();
                    if (m_goal->inconsistent()) 
                        goto end;
                }
                if (!m_modified)
                    goto end;
                m_subst->reset();
                m_r.set_substitution(m_subst.get()); // reset, but keep substitution
                m_modified   = false;
                m_occs(*m_goal);
                m_idx        = 0;
                size         = m_goal->size();
                forward      = true;
            }
            round++;
            if (round >= m_max_rounds)
                break;
            IF_VERBOSE(100, verbose_stream() << "starting new round, goal size: " << m_goal->num_exprs() << std::endl;);
            TRACE(propagate_values, tout << "round finished\n"; m_goal->display(tout); tout << "\n";);
        }
    end:
        m_goal->elim_redundancies();
        m_goal->inc_depth();
        result.push_back(m_goal);
        SASSERT(m_goal->is_well_formed());
        TRACE(propagate_values, tout << "end\n"; m_goal->display(tout););
        TRACE(propagate_values_core, m_goal->display_with_dependencies(tout););
        m_goal = nullptr;
    }
    
public:
    propagate_values_tactic(ast_manager & m, params_ref const & p):
        m(m),
        m_r(m, p),
        m_goal(nullptr),
        m_occs(m, true /* track atoms */),
        m_params(p) {
        updt_params_core(p);
        m_r.set_flat_and_or(false);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(propagate_values_tactic, m, m_params);
    }

    char const* name() const override { return "propagate_values"; }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_r.updt_params(p);
        updt_params_core(m_params);
    }

    void collect_param_descrs(param_descrs & r) override {
        th_rewriter::get_param_descrs(r);
        r.insert("max_rounds", CPK_UINT, "maximum number of rounds.", "4");
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        try {
            run(in, result);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.what());
        }
    }
    
    void cleanup() override {
        m_r.cleanup();
        m_subst = nullptr;
        m_occs.cleanup();
    }
    
};
}

tactic * mk_propagate_values_tactic(ast_manager & m, params_ref const & p) {
    return alloc(propagate_values_tactic, m, p);
}
