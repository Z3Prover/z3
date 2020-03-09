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
namespace lp {
typedef unsigned var_index;
typedef unsigned constraint_index;
typedef unsigned row_index;
enum lconstraint_kind { LE = -2, LT = -1 , GE = 2, GT = 1, EQ = 0, NE = 3 };
}
