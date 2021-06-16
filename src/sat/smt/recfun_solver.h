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

        scoped_ptr_vector<propagation_item> m_propagation_queue;
        unsigned                            m_qhead { 0 };

        void push_body_expand(expr* e) { push_prop(alloc(propagation_item, alloc(body_expansion, u(), to_app(e)))); }
        void push_case_expand(expr* e) { push_prop(alloc(propagation_item, alloc(case_expansion, u(), to_app(e)))); }
        void push_guard(expr* e) { push_prop(alloc(propagation_item, e)); }
        void push_c(expr_ref_vector const& core) { push_prop(alloc(propagation_item, core)); }
        void push_prop(propagation_item* p);

        bool is_enabled_guard(expr* guard) { return m_enabled_guards.contains(guard); }
        bool is_disabled_guard(expr* guard) { return m_disabled_guards.contains(guard); }

        recfun::util & u() const { return m_util; }
        bool is_defined(expr * f) const { return u().is_defined(f); }
        bool is_case_pred(expr * f) const { return u().is_case_pred(f); }

        bool is_defined(euf::enode * e) const { return is_defined(e->get_expr()); }
        bool is_case_pred(euf::enode * e) const { return is_case_pred(e->get_expr()); }


        expr_ref apply_args(vars const & vars, expr_ref_vector const & args, expr * e); 
        void assert_macro_axiom(case_expansion & e);
        void assert_case_axioms(case_expansion & e);
        void assert_body_axiom(body_expansion & e);
        void assert_guard(expr* guard, expr_ref_vector const& guards);
        void block_core(expr_ref_vector const& core);
        void disable_guard(expr* guard, expr_ref_vector const& guards);
        
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
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }
        void collect_statistics(statistics& st) const override;
        euf::th_solver* clone(euf::solver& ctx) override;
        bool unit_propagate() override;
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool redundant) override;
        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;
        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;
        bool is_shared(euf::theory_var v) const override { return true; }
        void init_search() override {}
        bool should_research(sat::literal_vector const& core) override;
        void add_assumptions() override;
        bool tracking_assumptions() override { return true; }
    };
}
