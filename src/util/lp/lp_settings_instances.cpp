/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <memory>
#include "util/vector.h"
#include "util/lp/lp_settings.hpp"
template bool lean::vectors_are_equal<double>(vector<double> const&, vector<double> const&);
template bool lean::vectors_are_equal<lean::mpq>(vector<lean::mpq > const&, vector<lean::mpq> const&);

