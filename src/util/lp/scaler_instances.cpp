/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/scaler.hpp"
template bool lp::scaler<double, double>::scale();
template bool lp::scaler<lp::mpq, lp::mpq>::scale();
