/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    user_propagator.h

Abstract:

    User-propagator plugin.
    Adds user plugins to propagate based on 
    terms receiving fixed values.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-17

Notes:

- could also be complemented with disequalities to fixed values to narrow range of variables.


--*/

#pragma once

#include "smt/smt_theory.h"

namespace smt {
    class user_propagator : public theory {
        void* m_user_context;
        std::function<void(void*, unsigned, expr*)> m_fixed_eh;
        std::function<void(void*)>                  m_push_eh;
        std::function<void(void*, unsigned)>        m_pop_eh;
        std::function<void*(void*)>                 m_fresh_eh;
        struct prop_info {
            unsigned_vector m_ids;
            expr_ref        m_conseq;
            prop_info(unsigned sz, unsigned const* ids, expr_ref const& c):
                m_ids(sz, ids),
                m_conseq(c)
            {}
        };
        unsigned               m_qhead;
        vector<prop_info>      m_prop;
        unsigned_vector        m_prop_lim;
        vector<literal_vector> m_id2justification;
        unsigned               m_num_scopes;

        void force_push();

    public:
        user_propagator(context& ctx);
        
        ~user_propagator() override {}

        /*
         * \brief initial setup for user propagator.
         */
        void add(
            void* ctx, 
            std::function<void(void*, unsigned, expr*)>& fixed_eh,
            std::function<void(void*)>&                  push_eh,
            std::function<void(void*, unsigned)>&        pop_eh,
            std::function<void*(void*)>&                 fresh_eh) {
            m_user_context = ctx;
            m_fixed_eh     = fixed_eh;
            m_push_eh      = push_eh;
            m_pop_eh       = pop_eh;
            m_fresh_eh     = fresh_eh;
        }

        unsigned add_expr(expr* e);

        void add_propagation(unsigned sz, unsigned const* ids, expr* conseq) {
            m_prop.push_back(prop_info(sz, ids, expr_ref(conseq, m)));
        }

        void new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits);

        theory * mk_fresh(context * new_ctx) override { 
            auto* th = alloc(user_propagator, *new_ctx); 
            void* ctx = m_fresh_eh(m_user_context);
            th->add(ctx, m_fixed_eh, m_push_eh, m_pop_eh, m_fresh_eh);
            return th;
        }
        bool internalize_atom(app * atom, bool gate_ctx) override { UNREACHABLE(); return false; }
        bool internalize_term(app * term) override { UNREACHABLE(); return false; }
        void new_eq_eh(theory_var v1, theory_var v2) override { }
        void new_diseq_eh(theory_var v1, theory_var v2) override { }
        bool use_diseqs() const override { return false; }
        bool build_models() const override { return false; }
        final_check_status final_check_eh() override { return FC_DONE; }
        void reset_eh() override {}
        void assign_eh(bool_var v, bool is_true) override { }
        void init_search_eh() override {}
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override {}
        void collect_statistics(::statistics & st) const override {}
        model_value_proc * mk_value(enode * n, model_generator & mg) override { return nullptr; }
        void init_model(model_generator & m) override {}
        bool include_func_interp(func_decl* f) override { return false; }
        bool can_propagate() override;
        void propagate() override; 
        void display(std::ostream& out) const {}
    };
};
