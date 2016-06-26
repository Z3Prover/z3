
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#ifndef QE_ARITH_H_
#define QE_ARITH_H_

#include "model.h"
#include "arith_decl_plugin.h"
#include "qe_mbp.h"

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
        virtual ~arith_project_plugin();
        virtual bool operator()(model& model, app* var, app_ref_vector& vars, expr_ref_vector& lits);
        virtual bool solve(model& model, app_ref_vector& vars, expr_ref_vector& lits);
        virtual family_id get_family_id();
        virtual void operator()(model& model, app_ref_vector& vars, expr_ref_vector& lits);


        opt::inf_eps maximize(expr_ref_vector const& fmls, model& mdl, app* t, expr_ref& ge, expr_ref& gt);
    };

    bool arith_project(model& model, app* var, expr_ref_vector& lits);


};

#endif
