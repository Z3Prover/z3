/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/scaler.hpp"
template bool lean::scaler<double, double>::scale();
template bool lean::scaler<lean::mpq, lean::mpq>::scale();
