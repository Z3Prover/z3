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
#include <string>
#include "util/debug.h"
namespace lp {
    enum class lia_move {
        sat,
        branch,
        cut,
        conflict,
        continue_with_check,
        undef,
        cancelled
    };
    inline std::string lia_move_to_string(lia_move m) {
        switch (m) {
        case lia_move::sat:
            return "sat";
        case lia_move::branch:
            return "branch";
        case lia_move::cut:
            return "cut";
        case lia_move::conflict:
            return "conflict";
        case lia_move::continue_with_check:
            return "continue_with_check";
        case lia_move::undef:
            return "undef";
        case lia_move::cancelled:
            return "cancelled";
        default:
            UNREACHABLE();
        };
        return "strange";
    }

    inline lia_move join(lia_move r1, lia_move r2) {
        if (r1 == r2)
            return r1;
        if (r1 == lia_move::undef)
            return r2;
        if (r2 == lia_move::undef)
            return r1;
        if (r1 == lia_move::conflict || r2 == lia_move::conflict)
            return lia_move::conflict;
        if (r1 == lia_move::cancelled || r2 == lia_move::cancelled)
            return lia_move::cancelled;
        if (r1 == lia_move::sat || r2 == lia_move::sat)
            return lia_move::sat;
        if (r1 == lia_move::continue_with_check || r2 == lia_move::continue_with_check)
            return lia_move::continue_with_check;
        if (r1 == lia_move::cut || r2 == lia_move::cut)
            return lia_move::cut;
        if (r1 == lia_move::branch || r2 == lia_move::branch)
            return lia_move::branch;
        UNREACHABLE();
        return r1;
    }

    inline std::ostream& operator<<(std::ostream& out, lia_move const& m) {
        return out << lia_move_to_string(m);
    }
}
