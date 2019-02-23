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
    unsigned num_vars;        // [in]
    unsigned num_clauses;     // [in]
    unsigned sz;              // [in]
    int * clauses;            // [in] array of size sz. Clauses are separated by 0. There are num_clauses in the array
    double* var_scores;       // [out] array of length num_vars with variable scores
    double  is_sat;           // [out] prediction if the problem is sat
    double* clause_scores;    // [out] array of length num_clauses                
};

typedef void (*neuro_predictor)(void* state, neuro_prediction* p);
