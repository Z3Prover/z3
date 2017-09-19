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
#include "util/vector.h"
#include "util/debug.h"
#include "util/lp/lp_settings.h"
#include <unordered_map>
namespace lp {
typedef std::unordered_map<unsigned, non_basic_column_value_position> lar_solution_signature;
}
