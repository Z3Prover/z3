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
#include "tactic/tactic.h"
#include "ast/simplifiers/dependent_expr_state.h"

class dependent_expr_state_tactic : public tactic, public dependent_expr_state {
    ast_manager&    m;
    params_ref      m_params;
    std::string     m_name;
    ref<dependent_expr_simplifier_factory>  m_factory;
    scoped_ptr<dependent_expr_simplifier>   m_simp;
    goal_ref        m_goal;
    dependent_expr  m_dep;

    void init() {
        if (!m_simp)
            m_simp = m_factory->mk(m, m_params, *this);
    }

public:

    dependent_expr_state_tactic(ast_manager& m, params_ref const& p, dependent_expr_simplifier_factory* f, char const* name):
        m(m),
        m_params(p),
        m_name(name),
        m_factory(f),
        m_simp(f->mk(m, p, *this)),
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
        if (in->proofs_enabled())
            throw tactic_exception("tactic does not support low level proofs");
        init();
        tactic_report report(name(), *in);
        m_goal = in.get();
        m_simp->reduce();
        m_goal->inc_depth();
        if (in->models_enabled())
            in->set(m_simp->get_model_converter().get());
        result.push_back(in.get());        
    }

    void cleanup() override {
    }

    void collect_statistics(statistics & st) const override {
        if (m_simp)
            m_simp->collect_statistics(st);
    }
    
    void reset_statistics() override {
        if (m_simp)
            m_simp->reset_statistics();
    }
};

