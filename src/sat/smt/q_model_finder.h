/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_finder.h

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-29

Notes:
   
    Derives from smt/smt_model_finder.cpp

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "solver/solver.h"

namespace euf {
    class solver;
}

namespace q {

    class model_finder {
        euf::solver&                           ctx;        
        ast_manager&                           m;

    public:

        model_finder(euf::solver& ctx);

        expr_ref inv_term(model& mdl, quantifier* q, unsigned idx, expr* value, unsigned& generation);

        void restrict_instantiations(::solver& s, model& mdl, quantifier* q, expr_ref_vector const& vars);
        
    };

}
