/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    dependent_expr_state_tactic.h

Abstract:

    The dependent_expr_state_tactic creates a tactic from a dependent_expr_simplifier.
    It relies on a factory for building simplifiers.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/
#pragma once
#include "tactic/tactic.h"
#include "ast/simplifiers/dependent_expr_state.h"

class dependent_expr_state_tactic : public tactic, public dependent_expr_state {
public:
    using factoryTy = dependent_expr_simplifier(*(*)(ast_manager& m, params_ref const& p, dependent_expr_state& s));
private:
    ast_manager& m;
    params_ref      m_params;
    trail_stack     m_trail;
    goal_ref        m_goal;
    dependent_expr  m_dep;
    statistics      m_st;
    factoryTy       m_factory;
    expr_ref_vector m_frozen;
    scoped_ptr<dependent_expr_simplifier>   m_simp;
    scoped_ptr<model_reconstruction_trail>  m_model_trail;
    bool m_updated = false;

    void init() {
        if (!m_simp) {
            m_simp = m_factory(m, m_params, *this);
            m_st.reset();
            push();
            for (expr* e : m_frozen)
                freeze(e);
        }
        if (!m_model_trail)
            m_model_trail = alloc(model_reconstruction_trail, m, m_trail);
    }

public:

    dependent_expr_state_tactic(ast_manager& m, params_ref const& p, factoryTy f) :
        dependent_expr_state(m),
        m(m),
        m_params(p),
        m_dep(m, m.mk_true(), nullptr, nullptr),
        m_factory(f),
        m_frozen(m)
    {}

    ~dependent_expr_state_tactic() override {
        if (m_simp)
            pop(1);
    }
    
    /**
    * size(), [](), update() and inconsistent() implement the abstract interface of dependent_expr_state
    */
    unsigned qtail() const override { return m_goal->size(); }

    dependent_expr const& operator[](unsigned i) override {
        m_dep = dependent_expr(m, m_goal->form(i), m_goal->pr(i), m_goal->dep(i));
        return m_dep;
    }

    void update(unsigned i, dependent_expr const& j) override {
        if (inconsistent())
            return;
        m_updated = true;
        auto [f, p, d] = j();
        m_goal->update(i, f, p, d);
    }

    void add(dependent_expr const& j) override {
        if (inconsistent())
            return;
        m_updated = true;
        auto [f, p, d] = j();
        m_goal->assert_expr(f, p, d);
    }

    bool inconsistent() override {
        return m_goal->inconsistent();
    }

    model_reconstruction_trail& model_trail() override {
        return *m_model_trail;
    }

    char const* name() const override { return m_simp ? m_simp->name() : "null"; }

    bool updated() override { return m_updated; }

    void reset_updated() override { m_updated = false; }

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        init();
        m_simp->updt_params(m_params);
    }

    void collect_param_descrs(param_descrs& r) override {
        init();
        m_simp->collect_param_descrs(r);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(dependent_expr_state_tactic, m, m_params, m_factory);
    }

    void operator()(goal_ref const& in,
        goal_ref_buffer& result) override {
        init();
        statistics_report sreport(*this);
        tactic_report report(name(), *in);
        m_goal = in.get();
        try {
            if (!in->proofs_enabled() || m_simp->supports_proofs())
                m_simp->reduce();
        }
        catch (rewriter_exception& ex) {
            throw tactic_exception(ex.what());
        }
        m_goal->elim_true();
        m_goal->elim_redundancies();
        m_goal->inc_depth();
        if (in->models_enabled())
            in->add(m_model_trail->get_model_converter().get());
        result.push_back(in.get());
        cleanup();
    }

    void collect_statistics(statistics& st) const override {
        if (m_simp)
            m_simp->collect_statistics(st);
        st.copy(m_st);
    }

    void cleanup() override {
        if (m_simp) {
            m_simp->collect_statistics(m_st);
            pop(1);
        }
        m_simp = nullptr;
        m_model_trail = nullptr;
        m_goal = nullptr;
        m_dep = dependent_expr(m, m.mk_true(), nullptr, nullptr);
    }

    void reset_statistics() override {
        if (m_simp)
            m_simp->reset_statistics();
        m_st.reset();
    }

    void user_propagate_register_expr(expr* e) override {
        freeze(e);
        m_frozen.push_back(e);
    }

    void user_propagate_clear() override {
        if (m_simp) {
            pop(1);
            push();
        }
        m_frozen.reset();
    }
};
