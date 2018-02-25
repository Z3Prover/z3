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
#include "util/lp/scaler_def.h"
template bool lp::scaler<double, double>::scale();
template bool lp::scaler<lp::mpq, lp::mpq>::scale();
