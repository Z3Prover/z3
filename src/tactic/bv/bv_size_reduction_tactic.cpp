/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    bv_size_reduction_tactic.cpp

Abstract:

    Reduce the number of bits used to encode constants, by using signed bounds.
    Example: suppose x is a bit-vector of size 8, and we have
    signed bounds for x such that:
        -2 <= x <= 2
    Then, x can be replaced by  ((sign-extend 5) k)
    where k is a fresh bit-vector constant of size 3.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include "tactic/bv/bv_size_reduction_tactic.h"
