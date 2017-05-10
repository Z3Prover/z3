/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/debug.h"
#include "util/lp/lp_settings.h"
#include <unordered_map>
namespace lean {
typedef std::unordered_map<unsigned, non_basic_column_value_position> lar_solution_signature;
}
