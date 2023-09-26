/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    theory_polymorphism.h

Abstract:

    Plugin for handling polymorphism 
    The plugin instantiates polymorphic axioms based on occurrences of polymorphic functions in other axioms.
    It uses blocking literals to restart search when there are new axioms that can be instantiated.

Author:

    Nikolaj Bjorner (nbjorner) 2013-07-11

--*/
#pragma once

#include "ast/polymorphism_inst.h"
#include "smt/smt_theory.h"

namespace smt {

    class theory_polymorphism : public theory {
        trail_stack        m_trail;
        polymorphism::inst m_inst;
        expr_ref           m_assumption;
        unsigned           m_qhead = 0;
        bool               m_pending = true;
        
        bool internalize_atom(app*, bool) override { return false; }
        bool internalize_term(app*) override { return false; }
        void new_eq_eh(theory_var, theory_var) override { }
        void new_diseq_eh(theory_var, theory_var) override {}
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_polymorphism, *new_ctx); }
        char const * get_name() const override { return "polymorphism"; }
        void display(std::ostream& out) const override {}

        void push_scope_eh() override {
            m_trail.push_scope();
        }

        void pop_scope_eh(unsigned n) override {
            m_trail.pop_scope(n);
        }

        bool can_propagate() override {
            return m_pending;
        }

        /**
        * Assert instances of polymorphic axioms
        */
        void propagate() override {
            if (!m_pending)
                return;
            m_pending = false;
            vector<polymorphism::instantiation> instances;
            m_inst.instantiate(instances);
            if (instances.empty())
                return;
            for (auto const& [orig, inst, sub] : instances) 
                ctx.add_asserted(inst);
            ctx.internalize_assertions();
        }

        final_check_status final_check_eh() override {
            if (m_inst.pending()) 
                ctx.assign(~mk_literal(m_assumption), nullptr);
            return FC_DONE;
        }

        void add_theory_assumptions(expr_ref_vector & assumptions) override {
            if (m_qhead == ctx.get_num_asserted_formulas())
                return;
            m_assumption = m.mk_fresh_const("poly", m.mk_bool_sort());
            assumptions.push_back(m_assumption);
            ctx.push_trail(value_trail(m_qhead));
            for (; m_qhead < ctx.get_num_asserted_formulas(); ++m_qhead)
                m_inst.add(ctx.get_asserted_formula(m_qhead));
            m_pending = true;
        }

        bool should_research(expr_ref_vector & assumptions) override {
            for (auto * a : assumptions)
                if (a == m_assumption)
                    return true;
            return false;
        }


    public:
        theory_polymorphism(context& ctx):
            theory(ctx, poly_family_id),
            m_inst(ctx.get_manager(), m_trail),
            m_assumption(ctx.get_manager()) {}
        
        void init_model(model_generator & mg) override { }
    };

};


