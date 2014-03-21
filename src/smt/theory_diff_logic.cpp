/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    theory_diff_logic.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-04-21.
    Nikolaj Bjorner (nbjorner) 2008-05-05

Revision History:

--*/
#include "theory_diff_logic.h"

#include"rational.h"
#include"theory_diff_logic_def.h"
#include"sparse_matrix_def.h"

namespace smt {

template class theory_diff_logic<idl_ext>;
template class theory_diff_logic<sidl_ext>;
template class theory_diff_logic<rdl_ext>;
template class theory_diff_logic<srdl_ext>;


};

namespace simplex {
template class simplex<mpq_ext>;
template class sparse_matrix<mpq_ext>;
};
