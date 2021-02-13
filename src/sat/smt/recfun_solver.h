/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    recfun_solver.h

Abstract:

    Recursive function solver plugin

Author:

    Simon Cruanes December 2017
    Nikolaj Bjorner (nbjorner) 2021-02-09

--*/
#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/ast_trail.h"
#include "sat/smt/sat_th.h"


namespace euf {
    class solver;
}

namespace recfun {

    class solver : public euf::th_euf_solver {

        struct stats {
            unsigned m_case_expansions, m_body_expansions, m_macro_expansions;
            void reset() { memset(this, 0, sizeof(stats)); }
            stats() { reset(); }
        };
        
        recfun::decl::plugin&   m_plugin;
        recfun::util&           m_util;
        stats                   m_stats;

        // book-keeping for depth of predicates
        expr_ref_vector          m_disabled_guards;
        expr_ref_vector          m_enabled_guards;
        obj_map<expr, expr_ref_vector*> m_guard2pending;
        obj_map<expr, unsigned>  m_pred_depth;
        expr_ref_vector          m_preds;
        unsigned_vector          m_preds_lim;
        unsigned                 m_num_rounds { 0 };

        struct propagation_item {
            case_expansion*            m_case { nullptr };
            body_expansion*            m_body { nullptr };
            sat::literal_vector        m_clause;
            expr*                      m_guard { nullptr };

            ~propagation_item() {
                dealloc(m_case);
                dealloc(m_body);
            }

            propagation_item(expr* guard):
                m_guard(guard) 
            {}

            propagation_item(sat::literal_vector const& clause):
                m_clause(clause)
            {}

            propagation_item(body_expansion* b):
                m_body(b)
            {}
            propagation_item(case_expansion* c):
                m_case(c)
            {}

            bool is_guard() const { return m_guard != nullptr; }
            bool is_clause() const { return !m_clause.empty(); }
            bool is_case() const { return m_case != nullptr; }
            bool is_body() const { return m_body != nullptr; }            
        };
        scoped_ptr_vector<propagation_item> m_propagation_queue;
        unsigned                            m_qhead { 0 };

        void push_body_expand(expr* e);
        void push_case_expand(expr* e);

        bool is_enabled_guard(expr* guard) { expr_ref ng(m.mk_not(guard), m); return m_enabled_guards.contains(ng); }
        bool is_disabled_guard(expr* guard) { return m_disabled_guards.contains(guard); }

        recfun::util & u() const { return m_util; }
        bool is_defined(expr * f) const { return u().is_defined(f); }
        bool is_case_pred(expr * f) const { return u().is_case_pred(f); }

        bool is_defined(euf::enode * e) const { return is_defined(e->get_expr()); }
        bool is_case_pred(euf::enode * e) const { return is_case_pred(e->get_expr()); }

        void activate_guard(expr* guard, expr_ref_vector const& guards);

        expr_ref apply_args(vars const & vars, expr_ref_vector const & args, expr * e); //!< substitute variables by args
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);

        void add_induction_lemmas(unsigned depth);
        void disable_guard(expr* guard, expr_ref_vector const& guards);
        unsigned get_depth(expr* e);
        void set_depth(unsigned d, expr* e);
        void set_depth_rec(unsigned d, expr* e);
        
        sat::literal mk_eq_lit(expr* l, expr* r);
        bool is_standard_order(recfun::vars const& vars) const { 
            return vars.empty() || vars[vars.size()-1]->get_idx() == 0;
        }

        void reset();
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;


    public:

        solver(euf::solver& ctx);
        ~solver() override;
        bool is_external(sat::bool_var v) override { return false; }
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override;
        void asserted(sat::literal l) override;
        sat::check_result check() override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return display_constraint(out, idx); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        euf::theory_var mk_var(euf::enode* n) override;
        void init_search() override;
        void finalize_model(model& mdl) override;
        bool is_shared(euf::theory_var v) const override { return true; }
    };
}
