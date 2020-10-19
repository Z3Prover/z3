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

    /***
    * An EUF inverter provides two services:
    * 1. It inverts an uninterpreted function application f(s1,s2) with 'value' to a ground term evaluating to the same 
    * 2. It adds constraints for arguments to s_i with 'value' to be within the bounds of the model value.
    */
    class euf_inverter {
    public:
        virtual expr* invert_app(app* t, expr* value) = 0;
        virtual expr* invert_arg(app* t, unsigned i, expr* value) = 0;
    };

    class project_plugin {
        ast_manager&     m;
        expr_mark        m_visited;
        ptr_vector<expr> m_to_visit;
        expr_mark        m_bool_visited;
        expr_mark        m_non_ground;
        expr_ref_vector  m_cache, m_args;

        void extract_bools(model_evaluator& eval, expr_ref_vector& fmls, unsigned i, expr* fml, bool is_true);
        void visit_app(expr* e);
        bool visit_ite(model_evaluator& eval, expr* e, expr_ref_vector& fmls);
        bool visit_bool(model_evaluator& eval, expr* e, expr_ref_vector& fmls);
        bool is_true(model_evaluator& eval, expr* e);

        // over-approximation
        bool contains_uninterpreted(expr* v) { return true; }

        void push_back(expr_ref_vector& lits, expr* lit);

        void mark_non_ground(app_ref_vector const& vars, expr_ref_vector const& fmls);

        expr* purify(euf_inverter& inv, model_evaluator& eval, expr* e, expr_ref_vector& lits);
        void purify_app(euf_inverter& inv, model_evaluator& eval, app* t, expr_ref_vector& lits);

    public:
        project_plugin(ast_manager& m) :m(m), m_cache(m), m_args(m) {}
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

        /*
        * Purify literals into linear inequalities or constraints without arithmetic variables.
        */
        void purify(euf_inverter& inv, model& model, app_ref_vector const& vars, expr_ref_vector& fmls);

        static expr_ref pick_equality(ast_manager& m, model& model, expr* t);
        static void erase(expr_ref_vector& lits, unsigned& i);

        static void mark_rec(expr_mark& visited, expr* e);
        static void mark_rec(expr_mark& visited, expr_ref_vector const& es);
    };
}

