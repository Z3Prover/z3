/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <memory>
#include "util/vector.h"
#include "util/lp/lp_settings.hpp"
template bool lp::vectors_are_equal<double>(vector<double> const&, vector<double> const&);
template bool lp::vectors_are_equal<lp::mpq>(vector<lp::mpq > const&, vector<lp::mpq> const&);

