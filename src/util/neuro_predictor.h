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
#pragma once

struct neuro_prediction {
    unsigned n_vars;              // [in] number of variables
    unsigned n_clauses;           // [in] number of clauses
    unsigned n_cells;             // [in] number of cells
    float    v_itau;              // [in] variable itau
    float    c_itau;              // [in] clause itau
    unsigned* C_idxs;             // [in n_cells] clause indices
    unsigned* L_idxs;             // [in n_cells] literal indices
    float* pi_march_ps;           // [out n_vars] cube prediction
    float* pi_core_var_ps;        // [out n_vars] membership of core
    float* pi_core_clause_ps;     // [out n_clauses] membership of core
    float* pi_model_ps;           // [out n_vars] variable valuation
};

// callback returns true on success, false on failure.
typedef bool neuro_predictor(void* state, neuro_prediction* p);

