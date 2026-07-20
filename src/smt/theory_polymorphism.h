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

        final_check_status final_check_eh(unsigned) override {
            if (m_inst.pending()) {
                // There are still polymorphic axioms to instantiate. Force the
                // solver to fail under the theory assumption so that a new
                // research round (see should_research) can assert the new
                // instances. Assigning the negation of the (already true)
                // assumption creates a conflict, so we must return FC_CONTINUE
                // to let conflict resolution turn it into l_false; returning
                // FC_DONE here would report l_true while the context is
                // inconsistent, violating a core search invariant.
                ctx.assign(~mk_literal(m_assumption), nullptr);
                return FC_CONTINUE;
            }
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

        ~theory_polymorphism() override {
            // Undo level-0 trail items (e.g. the inc_ref balancing entries that
            // m_inst pushes for m_from_instantiation). trail_stack's destructor
            // does not call reset(), so without this the references those items
            // hold would leak when the theory is destroyed.
            m_trail.reset();
        }
        
        void init_model(model_generator & mg) override { }
    };

}


