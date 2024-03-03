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
#pragma once

#include <sstream>
#include <limits.h>
#include "util/debug.h"
#include "util/dependency.h"

namespace nla {
    class core;
}

namespace lp {

typedef unsigned constraint_index;
typedef unsigned row_index;
enum lconstraint_kind { LE = -2, LT = -1 , GE = 2, GT = 1, EQ = 0, NE = 3 };
typedef unsigned lpvar;
const lpvar null_lpvar = UINT_MAX;
const constraint_index null_ci = UINT_MAX;
}


