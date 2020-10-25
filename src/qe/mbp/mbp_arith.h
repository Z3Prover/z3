
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#pragma once

#include "ast/arith_decl_plugin.h"
#include "model/model.h"
#include "qe/mbp/mbp_plugin.h"

namespace mbp {

    /**
       Loos-Weispfenning model-based projection for a basic conjunction.
       Lits is a vector of literals.
       return vector of variables that could not be projected.
     */

    class arith_project_plugin : public project_plugin {
        struct imp;
        imp* m_imp;        
    public:
        arith_project_plugin(ast_manager& m);
        ~arith_project_plugin() override;
        
        bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits) override;
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override { return false; }
        family_id get_family_id() override;
        void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        vector<def> project(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        void saturate(model& model, func_decl_ref_vector const& shared, expr_ref_vector& lits) override { UNREACHABLE(); }

        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);

        /**
         * \brief check if formulas are purified, or leave it to caller to ensure that
         * arithmetic variables nested under foreign functions are handled properly.
         */
        void set_check_purified(bool check_purified);

        /**
        * \brief apply projection 
        */
        void set_apply_projection(bool apply_project);

    };

    bool arith_project(model& model, app* var, expr_ref_vector& lits);


};

