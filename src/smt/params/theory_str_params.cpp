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
}
