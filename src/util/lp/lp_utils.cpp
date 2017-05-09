/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lp_utils.h"
#ifdef lp_for_z3
namespace lean {
double numeric_traits<double>::g_zero = 0.0;
double numeric_traits<double>::g_one = 1.0;
}
#endif
