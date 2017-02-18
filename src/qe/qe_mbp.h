/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.h

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef __QE_MBP_H__
#define __QE_MBP_H__

#include "ast.h"
#include "params.h"
#include "model.h"
#include "model_based_opt.h"


namespace qe {

    struct cant_project {};

    class project_plugin {
    public:
        virtual ~project_plugin() {}
        virtual bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) = 0;
        virtual bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) = 0;
        virtual family_id get_family_id() = 0;
        virtual void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) { };

        static expr_ref pick_equality(ast_manager& m, model& model, expr* t);
        static void partition_values(model& model, expr_ref_vector const& vals, expr_ref_vector& lits);
        static void partition_args(model& model, app_ref_vector const& sels, expr_ref_vector& lits);
        static void erase(expr_ref_vector& lits, unsigned& i);
        static void push_back(expr_ref_vector& lits, expr* lit);
        static void mark_rec(expr_mark& visited, expr* e);
        static void mark_rec(expr_mark& visited, expr_ref_vector const& es);
    };

    class mbp {
        class impl;
        impl * m_impl;
    public:
        mbp(ast_manager& m);
        
        ~mbp();
        
        /**
           \brief
           Apply model-based qe on constants provided as vector of variables. 
           Return the updated formula and updated set of variables that were not eliminated.           
        */
        void operator()(bool force_elim, app_ref_vector& vars, model& mdl, expr_ref_vector& fmls);

        /**
           \brief
           Solve as many variables as possible using "cheap" quantifier elimination"
        */
        void solve(model& model, app_ref_vector& vars, expr_ref_vector& lits);

        /**
           \brief 
           Extract literals from formulas based on model.
         */
        void extract_literals(model& model, expr_ref_vector& lits);

        /**
           \brief 
           Maximize objective t under current model for constraints in fmls.
         */
        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);
    };
}

#endif 
