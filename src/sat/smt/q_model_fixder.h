/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_fixer.h

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

    class model_fixer {
        euf::solver&                           ctx;        
        ast_manager&                           m;

    public:

        model_fixer(euf::solver& ctx);

        /**
         * Update model in order to best satisfy quantifiers.
         * For the array property fragment, update the model
         * such that the range of functions behaves monotonically 
         * based on regions over the inputs.
         */
        void operator()(model& mdl);
        
    };

}
