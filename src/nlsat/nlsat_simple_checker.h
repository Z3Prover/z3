/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_simple_checker.cpp

Abstract:

    Attempts to find a conflict by using simple polynomial forms.
Author:

    Mengyu Zhao (Linxi) and Shaowei Cai

Revision History:

--*/

#pragma once
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_clause.h"


namespace nlsat {
    class simple_checker {
        struct imp;
        imp *  m_imp;
    public:
        simple_checker(pmanager &_pm, anum_manager &_am, const clause_vector &_clauses, literal_vector &_learned_unit, const atom_vector &_atoms, const unsigned &_arith_var_num);
        ~simple_checker();
        bool operator()();
    };
}