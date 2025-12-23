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

#include <limits.h>
#include <sstream>
#include "util/debug.h"
#include "util/dependency.h"

namespace nla {
    class core;
}

namespace lp {

    typedef unsigned constraint_index;
    typedef unsigned row_index;
    enum lconstraint_kind { LE = -2, LT = -1, GE = 2, GT = 1, EQ = 0, NE = 3 };


    typedef unsigned lpvar;
    const lpvar null_lpvar = UINT_MAX;
    const constraint_index null_ci = UINT_MAX;
}  
// namespace lp

inline lp::lconstraint_kind join(lp::lconstraint_kind k1, lp::lconstraint_kind k2) {
    if (k1 == k2)
        return k1;
    if (k1 == lp::lconstraint_kind::EQ)
        return k2;
    if (k2 == lp::lconstraint_kind::EQ)
        return k1;
    if ((k1 == lp::lconstraint_kind::LE && k2 == lp::lconstraint_kind::LT) ||
        (k1 == lp::lconstraint_kind::LT && k2 == lp::lconstraint_kind::LE))
        return lp::lconstraint_kind::LT;
    if ((k1 == lp::lconstraint_kind::GE && k2 == lp::lconstraint_kind::GT) ||
        (k1 == lp::lconstraint_kind::GT && k2 == lp::lconstraint_kind::GE))
        return lp::lconstraint_kind::GT;
    UNREACHABLE();
    return k1;
}

inline lp::lconstraint_kind meet(lp::lconstraint_kind k1, lp::lconstraint_kind k2) {
    if (k1 == k2)
        return k1;
    if (k1 == lp::lconstraint_kind::EQ)
        return k1;
    if (k2 == lp::lconstraint_kind::EQ)
        return k2;
    if ((k1 == lp::lconstraint_kind::LE && k2 == lp::lconstraint_kind::LT) ||
        (k1 == lp::lconstraint_kind::LT && k2 == lp::lconstraint_kind::LE))
        return lp::lconstraint_kind::LE;
    if ((k1 == lp::lconstraint_kind::GE && k2 == lp::lconstraint_kind::GT) ||
        (k1 == lp::lconstraint_kind::GT && k2 == lp::lconstraint_kind::GE))
        return lp::lconstraint_kind::GE;
    UNREACHABLE();
    return k1;
}
