/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
namespace lp {
enum class lia_move {
    sat,
    branch,
    cut,
    conflict,
    continue_with_check,
    undef,
    unsat
};
}
