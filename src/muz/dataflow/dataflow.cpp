/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    dataflow.cpp

Abstract:

    Generic bottom-up and top-down data-flow engine for analysis
    of rule sets.

Author:
    Henning Guenther (t-hennig)

--*/

#include "dataflow.h"
#include "reachability.h"

namespace datalog {

    const reachability_info reachability_info::null_fact;
}
