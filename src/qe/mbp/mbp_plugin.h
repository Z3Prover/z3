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
    public:
        virtual ~project_plugin() {}
        virtual bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) = 0;
        /**
           \brief partial solver.
        */
        virtual bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) = 0;
        virtual family_id get_family_id() = 0;

        virtual void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) { };

        /**
           \brief project vars modulo model, return set of definitions for eliminated variables.
           - vars in/out: returns variables that were not eliminated
           - lits in/out: returns projected literals
           - returns set of definitions
             (TBD: in triangular form, the last definition can be substituted into definitions that come before)
        */
        virtual vector<def> project(model& model, app_ref_vector& vars, expr_ref_vector& lits) = 0;

        /**
           \brief model based saturation. Saturates theory axioms to equi-satisfiable literals over EUF,
           such that 'shared' are not retained for EUF.
         */
        virtual void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) = 0;


        static expr_ref pick_equality(ast_manager& m, model& model, expr* t);
        static void erase(expr_ref_vector& lits, unsigned& i);
        static void push_back(expr_ref_vector& lits, expr* lit);
        static void mark_rec(expr_mark& visited, expr* e);
        static void mark_rec(expr_mark& visited, expr_ref_vector const& es);
    };
}

