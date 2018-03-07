/*++
Copyright (c) 2009 Microsoft Corporation

Module Name:

    stats.h

Abstract:

    Shared utilities for displaying statistics.

Author:

    nbjorner 2009-12-6

Revision History:

--*/

#ifndef STATS_H_
#define STATS_H_

#include<ostream>

inline void print_stat(std::ostream& out, char const* msg, unsigned num) {
    if (num > 0) {
        out << msg << num << "\n";
    }
}

inline void print_stat_f(std::ostream& out, char const* msg, float num) {
    if (num > 0.0f) {
        out << msg << num << "\n";
    }
}

#endif
