/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner, Lev Nachmanson
*/
#include "util/lp/cut_solver.h"
namespace lp {
template <typename T>
T cut_solver<T>::m_local_zero = zero_of_type<T>();
template <> int cut_solver<int>::m_local_zero = 0;
}

