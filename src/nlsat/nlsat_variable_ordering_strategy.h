/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    nlsat_simple_checker.cpp

Abstract:

    
Author:

    Mengyu Zhao (Linxi) and Shaowei Cai, ported from https://github.com/hybridSMT/hybridSMT.git

Revision History:

--*/

#pragma once
#include "nlsat/nlsat_clause.h"


#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"


namespace nlsat {
    
    typedef polynomial::manager::scoped_numeral scoped_numeral;
    typedef polynomial::manager::numeral_vector numeral_vector;
    

    enum Variable_Ordering_Strategy_Type {NONE = 0, BROWN, TRIANGULAR, ONLYPOLY, UNIVARIATE, FEATURE, ROOT};
    
    class vos_var_info_collector {
        struct imp;
        imp *  m_imp;
    public:
        vos_var_info_collector(pmanager & _pm, atom_vector const & atoms, unsigned _num_vars, unsigned _vos_type);
        ~vos_var_info_collector();
        void operator()(var_vector &perm);
        void collect(clause_vector const & cs);
    };
}