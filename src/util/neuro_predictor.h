/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    neuro_predictor.h

Abstract:

    struct definition for state of neuro predictor.

    Note: these type definitions must be kept in sync with the 
    mirrored definitions in z3_api.h. api_solver.cpp
    casts from the external to this internal type and 
    assumes the calling conventions are preserved.

Author:

    Nikolaj Bjorner (nbjorner) 2019-02-23.

Revision History:

--*/
#pragma once;

struct neuro_prediction {
    unsigned n_vars;              // [in] number of variables
    unsigned n_clauses;           // [in] number of clauses
    unsigned n_cells;             // [in] number of cells
    unsigned** LC_idxs;           // [in] [n_cells][2]
    float* pi_march_logits;       // [out n_vars] cube prediction
    float* pi_core_var_logits;    // [out n_vars] membership of core
    float* pi_core_clause_logits; // [out n_clauses] membership of core
    float* pi_model_logits;       // [out n_vars] variable valuation
    float is_sat_logit;           // [out]
};

// callback returns true on success, false on failure.
typedef bool neuro_predictor(void* state, neuro_prediction* p);

