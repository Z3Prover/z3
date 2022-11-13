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
    ast_manager&    m;
    params_ref      m_params;
    std::string     m_name;
    trail_stack     m_trail;
    goal_ref        m_goal;
    dependent_expr  m_dep;
    statistics      m_st;
    ref<dependent_expr_simplifier_factory>  m_factory;
    scoped_ptr<dependent_expr_simplifier>   m_simp;
    scoped_ptr<model_reconstruction_trail>  m_model_trail;

    void init() {
        if (!m_simp) {
            m_simp = m_factory->mk(m, m_params, *this);
            m_st.reset();
        }
        if (!m_model_trail)
            m_model_trail = alloc(model_reconstruction_trail, m, m_trail);
    }

public:

    dependent_expr_state_tactic(ast_manager& m, params_ref const& p, dependent_expr_simplifier_factory* f, char const* name):
        m(m),
        m_params(p),
        m_name(name),
        m_factory(f),
        m_simp(nullptr),
        m_dep(m, m.mk_true(), nullptr)
    {}

    /**
    * size(), [](), update() and inconsisent() implement the abstract interface of dependent_expr_state
    */
    unsigned size() const override { return m_goal->size(); }

    dependent_expr const& operator[](unsigned i) override {
        m_dep = dependent_expr(m, m_goal->form(i), m_goal->dep(i));
        return m_dep;
    }
    void update(unsigned i, dependent_expr const& j) override {
        auto [f, d] = j();
        m_goal->update(i, f, nullptr, d);
    }

    bool inconsistent() override {
        return m_goal->inconsistent();
    }

    model_reconstruction_trail& model_trail() override {
        return *m_model_trail;
    }
        
    char const* name() const override { return m_name.c_str(); }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        init();
        m_simp->updt_params(m_params);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(dependent_expr_state_tactic, m, m_params, m_factory.get(), name());
    }

    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        init();
        statistics_report sreport(*this);
        tactic_report report(name(), *in);
        m_goal = in.get();
        if (!in->proofs_enabled())
            m_simp->reduce();
        m_goal->elim_true();
        m_goal->inc_depth();
        if (in->models_enabled())
            in->add(m_model_trail->get_model_converter().get());
        result.push_back(in.get());   
        cleanup();
    }

    void cleanup() override {
        if (m_simp) 
            m_simp->collect_statistics(m_st);
        m_simp = nullptr;
        m_model_trail = nullptr;
    }

    void collect_statistics(statistics & st) const override {
        if (m_simp) 
            m_simp->collect_statistics(st);
        else
            st.copy(m_st);
    }
    
    void reset_statistics() override {
        if (m_simp)
            m_simp->reset_statistics();
        m_st.reset();
    }
};

