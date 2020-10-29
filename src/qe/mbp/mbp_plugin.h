/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    mbp_plugin.h

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "model/model.h"
#include "math/simplex/model_based_opt.h"


namespace mbp {

    struct cant_project {};

    struct def {
        expr_ref var, term;
        def(const expr_ref& v, expr_ref& t): var(v), term(t) {}
    };

    class project_plugin {
        ast_manager&     m;
        expr_mark        m_visited;
        ptr_vector<expr> m_to_visit;
        expr_mark        m_bool_visited;
        expr_mark        m_non_ground;
        expr_ref_vector  m_cache, m_args, m_pure_eqs;

        void extract_bools(model_evaluator& eval, expr_ref_vector& fmls, unsigned i, expr* fml, bool is_true);
        void visit_app(expr* e);
        bool visit_ite(model_evaluator& eval, expr* e, expr_ref_vector& fmls);
        bool visit_bool(model_evaluator& eval, expr* e, expr_ref_vector& fmls);
        bool is_true(model_evaluator& eval, expr* e);

        // over-approximation
        bool contains_uninterpreted(expr* v) { return true; }

        void push_back(expr_ref_vector& lits, expr* lit);

        void mark_non_ground(expr* e);

    public:
        project_plugin(ast_manager& m) :m(m), m_cache(m), m_args(m), m_pure_eqs(m) {}
        virtual ~project_plugin() {}
        virtual bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) { return false; }
        /**
           \brief partial solver.
        */
        virtual bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) { return false; }
        virtual family_id get_family_id() { return null_family_id; }

        virtual void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) { };

        /**
           \brief project vars modulo model, return set of definitions for eliminated variables.
           - vars in/out: returns variables that were not eliminated
           - lits in/out: returns projected literals
           - returns set of definitions
             (TBD: in triangular form, the last definition can be substituted into definitions that come before)
        */
        virtual vector<def> project(model& model, app_ref_vector& vars, expr_ref_vector& lits) { return vector<def>(); }

        /**
           \brief model based saturation. Saturates theory axioms to equi-satisfiable literals over EUF,
           such that 'shared' are not retained for EUF.
         */
        virtual void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) {}


        /*
        * extract top-level literals
        */
        void extract_literals(model& model, app_ref_vector const& vars, expr_ref_vector& fmls);

        static expr_ref pick_equality(ast_manager& m, model& model, expr* t);
        static void erase(expr_ref_vector& lits, unsigned& i);

        static void mark_rec(expr_mark& visited, expr* e);
        static void mark_rec(expr_mark& visited, expr_ref_vector const& es);

        /**
        * mark sub-terms in e whether they contain a variable from vars.
        */
        void mark_non_ground(app_ref_vector const& vars, expr* e) {
            for (app* v : vars)
                m_non_ground.mark(v);
            mark_non_ground(e);
        }

        bool is_non_ground(expr* t) const { return m_non_ground.is_marked(t); }

    };
}

