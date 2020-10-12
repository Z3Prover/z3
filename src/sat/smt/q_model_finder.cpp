/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_finder.cpp

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

Notes:
   
    Derives from smt/smt_model_finder.cpp

--*/

#include "sat/smt/q_model_finder.h"
#include "sat/smt/euf_solver.h"


namespace q {

    model_finder::model_finder(euf::solver& ctx):
        ctx(ctx), m(ctx.get_manager()) {}

    expr_ref model_finder::inv_term(model& mdl, quantifier* q, unsigned idx, expr* value, unsigned& generation) {
        return expr_ref(value, m);
    }

    void model_finder::restrict_instantiations(::solver& s, model& mdl, quantifier* q, expr_ref_vector const& vars) {
        
    }

    void model_finder::adjust_model(model& mdl) {

    }

}
