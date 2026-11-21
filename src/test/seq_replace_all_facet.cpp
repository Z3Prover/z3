/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_replace_all_facet.cpp (test)

Abstract:

    Unit test for `seq::replace_all_split::case_in_range`
    (ast/seq/seq_replace_all_facet.h): the 64-bit admissible-case-range
    check used by `apply_case` to bound `str.replace_all` case
    enumeration (NFV audit finding P12).

    Exercised directly as a pure arithmetic function, not through the
    full facet/solver, since reaching the affected boundary via a real
    pattern would require constructing a multi-gigabyte zstring (pattern
    length near 2^31) just to observe the admission check.

Author:

    Margus Veanes (veanes) 2026

--*/
#include "ast/seq/seq_replace_all_facet.h"
#include "util/debug.h"
#include <iostream>

namespace {

    static void tst_case_in_range_small_patterns() {
        // Ordinary, small pattern lengths: cases 0..2*len+1 are
        // admissible (production enumeration only ever starts at c=1
        // and counts up; c=0 is a mathematically valid but unused case
        // of the same formula), 2*len+2 onward are not.
        for (uint64_t len : {1ull, 2ull, 5ull, 100ull}) {
            for (uint64_t c = 0; c <= 2 * len + 1; ++c)
                ENSURE(seq::replace_all_split::case_in_range(c, len));
            ENSURE(!seq::replace_all_split::case_in_range(2 * len + 2, len));
            ENSURE(!seq::replace_all_split::case_in_range(2 * len + 3, len));
        }
    }

    // NFV audit finding P12: with pattern length and case number both
    // computed in unsigned 32-bit arithmetic, `2 * pattern_length + 2`
    // wraps for pattern lengths near 2^31, incorrectly rejecting every
    // case (including the always-valid case 1) for such a pattern.
    static void tst_case_in_range_no_overflow_near_uint_max() {
        uint64_t const huge_len = 2147483647ull; // 2^31 - 1
        // Mathematically correct threshold is 2*huge_len+2 = 4294967296,
        // one past 32-bit unsigned's range: the naive unsigned
        // computation wraps this to 0, which would make every case,
        // starting with case 1, falsely inadmissible.
        ENSURE(seq::replace_all_split::case_in_range(1, huge_len));
        ENSURE(seq::replace_all_split::case_in_range(2, huge_len));
        ENSURE(seq::replace_all_split::case_in_range(2 * huge_len + 1, huge_len));
        ENSURE(!seq::replace_all_split::case_in_range(2 * huge_len + 2, huge_len));

        // Largest possible 32-bit pattern length: the +2 in the
        // threshold must also not overflow.
        uint64_t const max_len = 4294967295ull; // UINT_MAX
        ENSURE(seq::replace_all_split::case_in_range(1, max_len));
        ENSURE(seq::replace_all_split::case_in_range(2 * max_len + 1, max_len));
        ENSURE(!seq::replace_all_split::case_in_range(2 * max_len + 2, max_len));
    }

}

void tst_seq_replace_all_facet() {
    tst_case_in_range_small_patterns();
    tst_case_in_range_no_overflow_near_uint_max();
    std::cout << "tst_seq_replace_all_facet: all tests passed\n";
}
