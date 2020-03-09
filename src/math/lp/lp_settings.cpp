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
#include "math/lp/lp_settings_def.h"
template bool lp::vectors_are_equal<double>(vector<double> const&, vector<double> const&);
template bool lp::vectors_are_equal<lp::mpq>(vector<lp::mpq > const&, vector<lp::mpq> const&);

