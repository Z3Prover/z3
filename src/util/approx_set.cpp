/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    approx_set.cpp

Abstract:

    Approximated sets.

Author:

    Leonardo de Moura (leonardo) 2007-03-02.

Revision History:

--*/

#include "util/approx_set.h"

void approx_set::display(std::ostream & out) const {
    out << "{";
    bool first = true;
    unsigned long long s = m_set;
    for (unsigned i = 0; i < approx_set_traits<unsigned long long>::capacity; i++) {
        if ((s & 1) != 0) {
            if (first) {
                first = false;
            }
            else {
                out << ", ";
            }
            out << i;
        }
        s = s >> 1;
    }
    out << "}";
}

unsigned approx_set::size() const {
    unsigned long long  tmp = m_set;
    unsigned r = 0;
    while (tmp > 0) {
        if ((tmp & 1) != 0) {
            r++;
        }
        tmp = tmp >> 1;
    }
    return r;
}

