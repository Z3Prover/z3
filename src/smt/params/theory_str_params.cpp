/*++
Module Name:

    theory_str_params.cpp

Abstract:

    Parameters for string theory plugin

Author:

    Murphy Berzish (mtrberzi) 2016-12-13

Revision History:

--*/

#include"theory_str_params.h"
#include"smt_params_helper.hpp"

void theory_str_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_AssertStrongerArrangements = p.str_strong_arrangements();
    m_AggressiveLengthTesting = p.str_aggressive_length_testing();
    m_AggressiveValueTesting = p.str_aggressive_value_testing();
    m_AggressiveUnrollTesting = p.str_aggressive_unroll_testing();
    m_UseFastLengthTesterCache = p.str_fast_length_tester_cache();
    m_UseFastValueTesterCache = p.str_fast_value_tester_cache();
    m_StringConstantCache = p.str_string_constant_cache();
}
