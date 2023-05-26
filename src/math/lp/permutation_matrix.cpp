/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#include <memory>
#include "util/vector.h"
#include "math/lp/permutation_matrix_def.h"
#include "math/lp/numeric_pair.h"
template void lp::permutation_matrix<lp::mpq, lp::mpq>::init(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq>>::init(unsigned int);

template lp::permutation_matrix<lp::mpq, lp::mpq>::permutation_matrix(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::transpose_from_left(unsigned int, unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::mpq>::transpose_from_right(unsigned int, unsigned int);
template lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::permutation_matrix(unsigned int);
template void lp::permutation_matrix<lp::mpq, lp::numeric_pair<lp::mpq> >::transpose_from_left(unsigned int, unsigned int);
