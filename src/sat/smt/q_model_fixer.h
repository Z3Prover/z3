/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_fixer.h

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-10-02

Notes:
   
    Derives from smt/smt_model_finder.cpp

    Contains exclusively functionality that adjusts a model to make it
    easier to satisfy relevant universally quantified literals.

--*/
#pragma once

#include "sat/smt/sat_th.h"
#include "solver/solver.h"
#include "model/model_macro_solver.h"

namespace euf {
    class solver;
}

namespace q {

    class solver;

    class model_fixer : public quantifier2macro_infos {
        euf::solver&        ctx;      
        solver&             qs;
        ast_manager&        m;
        obj_map<quantifier, quantifier_macro_info*> m_q2info;
        func_decl_dependencies m_dependencies;

    public:

        model_fixer(euf::solver& ctx, solver& qs);
        ~model_fixer() override {}

        /**
         * Update model in order to best satisfy quantifiers.
         * For the array property fragment, update the model
         * such that the range of functions behaves monotonically 
         * based on regions over the inputs.
         */
        void operator()(model& mdl);

        quantifier_macro_info* operator()(quantifier* q);
        
    };

}
