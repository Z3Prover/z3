/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    opt_preprocess.h

Abstract:
   
    Pre-processing for MaxSMT

    Find mutexes - at most 1 constraints and modify soft constraints and bounds.

Author:

    Nikolaj Bjorner (nbjorner) 2022-04-11

--*/

#pragma once

#include "opt/maxsmt.h"

namespace opt {

    class preprocess {
        ast_manager&     m;
        solver&          s;
        expr_ref_vector  m_trail;

        bool find_mutexes(vector<soft>& softs, rational& lower);
        void process_mutex(expr_ref_vector& mutex, obj_map<expr, rational>& new_soft, rational& lower);

    public:
        preprocess(solver& s);
        bool operator()(vector<soft>& soft, rational& lower);
    };
};
