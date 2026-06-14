/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    test/range_predicate.cpp

Abstract:

    Unit tests for the range-algebra value type seq::range_predicate.

    The tests exercise:
      * factory constructors and canonical-form invariants,
      * extensional equality and total ordering,
      * Boolean operations (|, &, ~, -, ^) on hand-picked instances,
      * exhaustive verification of de-Morgan and lattice laws on a
        small character domain, by enumerating every subset.

Author:

    Margus Veanes (veanes) 2026

--*/

#include "ast/rewriter/range_predicate.h"
#include "util/debug.h"
#include <cstdint>
#include <iostream>
#include <sstream>

using seq::range_predicate;

namespace {

    // Build a range_predicate from a bitmask over [0, max_char] for testing.
    range_predicate from_mask(uint64_t mask, unsigned max_char) {
        range_predicate r = range_predicate::empty(max_char);
        for (unsigned c = 0; c <= max_char; ++c)
            if ((mask >> c) & 1u)
                r = r | range_predicate::singleton(c, max_char);
        return r;
    }

    // Convert a range_predicate back to a bitmask for cross-checking.
    uint64_t to_mask(range_predicate const& r) {
        uint64_t mask = 0;
        for (unsigned c = 0; c <= r.max_char(); ++c)
            if (r.contains(c))
                mask |= (uint64_t(1) << c);
        return mask;
    }

    void test_factories() {
        auto e = range_predicate::empty(255);
        ENSURE(e.is_empty());
        ENSURE(!e.is_top());
        ENSURE(e.num_ranges() == 0);
        ENSURE(e.cardinality() == 0);

        auto t = range_predicate::top(255);
        ENSURE(!t.is_empty());
        ENSURE(t.is_top());
        ENSURE(t.num_ranges() == 1);
        ENSURE(t.cardinality() == 256);
        ENSURE(t.contains(0));
        ENSURE(t.contains(255));

        auto s = range_predicate::singleton(42, 255);
        ENSURE(s.num_ranges() == 1);
        ENSURE(s.cardinality() == 1);
        ENSURE(s.contains(42));
        ENSURE(!s.contains(41));
        unsigned c = 0;
        ENSURE(s.is_singleton(c));
        ENSURE(c == 42);

        auto r = range_predicate::range(10, 20, 255);
        ENSURE(r.num_ranges() == 1);
        ENSURE(r.cardinality() == 11);
        ENSURE(r.contains(10));
        ENSURE(r.contains(20));
        ENSURE(!r.contains(9));
        ENSURE(!r.contains(21));

        // Reversed bounds produce empty.
        auto bad = range_predicate::range(20, 10, 255);
        ENSURE(bad.is_empty());

        // Clipping at max_char.
        auto clipped = range_predicate::range(200, 1000, 255);
        ENSURE(clipped.num_ranges() == 1);
        ENSURE(clipped[0] == std::make_pair(200u, 255u));
    }

    void test_equality_and_order() {
        auto a = range_predicate::range(1, 5, 31);
        auto b = range_predicate::range(1, 5, 31);
        auto c = range_predicate::range(1, 6, 31);
        ENSURE(a == b);
        ENSURE(a != c);
        ENSURE(a.hash() == b.hash());
        ENSURE(a < c || c < a);
        ENSURE(!(a < a));

        auto empty = range_predicate::empty(31);
        ENSURE(empty < a);

        // Canonical merging of adjacent ranges.
        auto d = range_predicate::range(0, 4, 31) | range_predicate::range(5, 10, 31);
        auto e = range_predicate::range(0, 10, 31);
        ENSURE(d == e);
    }

    void test_union_intersection_hand() {
        unsigned const M = 31;
        auto a = range_predicate::range(0, 4, M) | range_predicate::range(10, 14, M);
        auto b = range_predicate::range(3, 11, M);

        auto u = a | b; // [0,14]
        ENSURE(u.num_ranges() == 1);
        ENSURE(u[0] == std::make_pair(0u, 14u));

        auto i = a & b; // [3,4] U [10,11]
        ENSURE(i.num_ranges() == 2);
        ENSURE(i[0] == std::make_pair(3u, 4u));
        ENSURE(i[1] == std::make_pair(10u, 11u));

        auto d = a - b; // [0,2] U [12,14]
        ENSURE(d.num_ranges() == 2);
        ENSURE(d[0] == std::make_pair(0u, 2u));
        ENSURE(d[1] == std::make_pair(12u, 14u));

        auto x = a ^ b; // [0,2] U [5,9] U [12,14]
        ENSURE(x.num_ranges() == 3);
        ENSURE(x[0] == std::make_pair(0u, 2u));
        ENSURE(x[1] == std::make_pair(5u, 9u));
        ENSURE(x[2] == std::make_pair(12u, 14u));
    }

    void test_complement_hand() {
        unsigned const M = 10;
        auto e = range_predicate::empty(M);
        ENSURE((~e).is_top());
        auto t = range_predicate::top(M);
        ENSURE((~t).is_empty());

        // ~([2,3] U [7,8]) = [0,1] U [4,6] U [9,10]
        auto a = range_predicate::range(2, 3, M) | range_predicate::range(7, 8, M);
        auto na = ~a;
        ENSURE(na.num_ranges() == 3);
        ENSURE(na[0] == std::make_pair(0u, 1u));
        ENSURE(na[1] == std::make_pair(4u, 6u));
        ENSURE(na[2] == std::make_pair(9u, 10u));

        // ~([0,4]) = [5,10]
        auto b = range_predicate::range(0, 4, M);
        auto nb = ~b;
        ENSURE(nb.num_ranges() == 1);
        ENSURE(nb[0] == std::make_pair(5u, 10u));

        // ~([5,10]) = [0,4]
        auto cnb = ~nb;
        ENSURE(cnb == b);
    }

    // Exhaustively verify the lattice / de-Morgan laws on a small domain
    // by enumerating every possible subset (bitmask).
    void test_exhaustive_laws() {
        unsigned const M = 5; // 6 characters -> 64 subsets
        unsigned const N = 1u << (M + 1);
        for (unsigned i = 0; i < N; ++i) {
            range_predicate A = from_mask(i, M);
            ENSURE(to_mask(A) == i);
            // ~ ~ A == A
            ENSURE(~~A == A);
            // A | ~A == top
            ENSURE((A | ~A).is_top());
            // A & ~A == empty
            ENSURE((A & ~A).is_empty());
            // cardinality matches popcount
            unsigned pop = 0;
            for (unsigned k = 0; k <= M; ++k) if ((i >> k) & 1u) ++pop;
            ENSURE(A.cardinality() == pop);
        }
        for (unsigned i = 0; i < N; ++i) {
            range_predicate A = from_mask(i, M);
            for (unsigned j = 0; j < N; ++j) {
                range_predicate B = from_mask(j, M);
                // Bitmask reference semantics.
                ENSURE(to_mask(A | B) == (i | j));
                ENSURE(to_mask(A & B) == (i & j));
                ENSURE(to_mask(A - B) == (i & ~j & ((1u << (M + 1)) - 1u)));
                ENSURE(to_mask(A ^ B) == (i ^ j));
                // de-Morgan
                ENSURE(~(A | B) == (~A & ~B));
                ENSURE(~(A & B) == (~A | ~B));
                // Commutativity
                ENSURE((A | B) == (B | A));
                ENSURE((A & B) == (B & A));
                // (A - B) == A & ~B
                ENSURE((A - B) == (A & ~B));
                // (A ^ B) == (A | B) - (A & B)
                ENSURE((A ^ B) == ((A | B) - (A & B)));
                // Extensional equality is reflexive on equal masks.
                if (i == j) {
                    ENSURE(A == B);
                    ENSURE(A.hash() == B.hash());
                }
            }
        }
    }

    void test_total_order_strict() {
        unsigned const M = 5;
        unsigned const N = 1u << (M + 1);
        // Strict total order: for any distinct A, B exactly one of A<B, B<A holds.
        for (unsigned i = 0; i < N; ++i) {
            range_predicate A = from_mask(i, M);
            ENSURE(!(A < A));
            for (unsigned j = i + 1; j < N; ++j) {
                range_predicate B = from_mask(j, M);
                bool lt = A < B;
                bool gt = B < A;
                ENSURE(lt != gt);
                ENSURE(lt || gt);
            }
        }
    }

    void test_display() {
        std::ostringstream oss;
        oss << range_predicate::empty(31);
        ENSURE(oss.str() == "[]");

        oss.str("");
        oss << range_predicate::range(3, 7, 31);
        ENSURE(oss.str() == "[3-7]");

        oss.str("");
        oss << range_predicate::singleton(9, 31);
        ENSURE(oss.str() == "[9]");

        oss.str("");
        auto p = range_predicate::range(0, 2, 31) | range_predicate::singleton(5, 31);
        oss << p;
        ENSURE(oss.str() == "[0-2,5]");
    }

}

void tst_range_predicate() {
    test_factories();
    test_equality_and_order();
    test_union_intersection_hand();
    test_complement_hand();
    test_exhaustive_laws();
    test_total_order_strict();
    test_display();
    std::cout << "range_predicate unit tests passed\n";
}
