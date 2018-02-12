
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#ifndef QE_ARITH_H_
#define QE_ARITH_H_

#include "model/model.h"
#include "ast/arith_decl_plugin.h"
#include "qe/qe_mbp.h"

namespace qe {

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
        bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;
        family_id get_family_id() override;
        void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits) override;


        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);
    };

    bool arith_project(model& model, app* var, expr_ref_vector& lits);


};

#endif
