/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_len_abs.cpp

Abstract:

    Unit tests for the ultimately periodic length abstraction.

    These exercise seq::len_abs directly, with no ast_manager and no rewriter, so
    they pin the arithmetic of the lattice itself.  The tests that check how the
    abstraction is derived from a regex live in tst_seq_rewriter.

--*/

#include "ast/seq_len_abs.h"
#include "util/debug.h"
#include <iostream>

namespace {

    using seq::len_abs;

    /* Membership in the concretization of the abstraction. */
    static bool admits(len_abs const& a, unsigned n) {
        return n >= a.lo() && n <= a.hi() && (a.residues() & (1ull << (n % a.period())));
    }

    /*
      Every operation must over-approximate, so whenever the concrete rule puts a
      length in the result the abstraction has to admit it.  This is the only
      property that matters for soundness; precision is checked separately.
    */
    static void check_sound_binary(len_abs const& x, len_abs const& y, len_abs const& r,
                                   bool sum, unsigned bound) {
        for (unsigned i = 0; i <= bound; ++i) {
            if (!admits(x, i))
                continue;
            if (!sum) {
                ENSURE(admits(r, i));                 // union: lengths of x carry over
                continue;
            }
            for (unsigned j = 0; j <= bound; ++j)
                if (admits(y, j))
                    ENSURE(admits(r, i + j));         // concat: sums carry over
        }
    }

    static void tst_basics() {
        len_abs top;
        ENSURE(top.is_trivial() && !top.is_empty());
        ENSURE(top.lo() == 0 && top.hi() == UINT_MAX);
        ENSURE(len_abs::empty().is_empty());
        ENSURE(len_abs::exact(7).lo() == 7 && len_abs::exact(7).hi() == 7);
        ENSURE(len_abs::exact(7).eff_period() == 0);  // singleton adapts to any period
        ENSURE(len_abs::exact(0).gcd() == 0);
    }

    static void tst_progression() {
        // The single arithmetic progression an automaton BFS produces: d + g*N.
        len_abs p = len_abs::progression(3, 4);
        ENSURE(p.lo() == 3 && p.period() == 4 && p.num_residues() == 1);
        ENSURE(admits(p, 3) && admits(p, 7) && admits(p, 11));
        ENSURE(!admits(p, 4) && !admits(p, 5) && !admits(p, 6));
        // stride 0 means the length is exactly d
        len_abs e = len_abs::progression(5, 0);
        ENSURE(e.lo() == 5 && e.hi() == 5);
        // an over-wide stride has to degrade rather than overflow the mask
        ENSURE(len_abs::progression(1, 1000).is_trivial());
    }

    static void tst_star_and_plus() {
        // (aaaa)* : lengths are the multiples of 4
        len_abs four = len_abs::exact(4);
        len_abs star4 = four.star();
        ENSURE(star4.period() == 4 && star4.num_residues() == 1);
        ENSURE(admits(star4, 0) && admits(star4, 4) && admits(star4, 8));
        ENSURE(!admits(star4, 1) && !admits(star4, 6));
        // (bbbbbb)* : multiples of 6.  Together with |z| + 1 = |w| this is the
        // cross-variable parity refutation, closed by the arithmetic gcd test.
        len_abs star6 = len_abs::exact(6).star();
        ENSURE(star6.period() == 6 && star6.num_residues() == 1);
        // a(aa)* : odd lengths
        len_abs odd = len_abs::exact(1).concat(len_abs::exact(2).star());
        ENSURE(odd.period() == 2 && odd.residues() == 0x2);
        ENSURE(admits(odd, 1) && admits(odd, 3) && !admits(odd, 2));
        // starring an odd-length language readmits every length, so it must go trivial
        ENSURE(odd.star().is_trivial());
        // plus keeps the lower bound, star does not
        ENSURE(four.plus().lo() == 4 && four.star().lo() == 0);
    }

    static void tst_concat() {
        len_abs star2 = len_abs::exact(2).star();      // even
        len_abs star3 = len_abs::exact(3).star();      // multiples of 3
        // even + multiple of 3: the sumset modulo gcd(2,3) = 1 is everything
        ENSURE(star2.concat(star3).is_trivial());
        // (ab)*a has odd length
        len_abs ab_star_a = star2.concat(len_abs::exact(1));
        ENSURE(ab_star_a.period() == 2 && ab_star_a.residues() == 0x2);
        check_sound_binary(star2, star3, star2.concat(star3), true, 24);
        check_sound_binary(star2, len_abs::exact(1), ab_star_a, true, 24);
    }

    static void tst_unite_beats_single_progression() {
        // (aa)* | (aaa)* -- a single progression d + g*N degrades to gcd(2,3) = 1 and
        // says nothing, while a residue set keeps {0,2,3,4} mod 6.
        len_abs u = len_abs::exact(2).star().unite(len_abs::exact(3).star());
        ENSURE(u.period() == 6);
        ENSURE(u.residues() == ((1ull << 0) | (1ull << 2) | (1ull << 3) | (1ull << 4)));
        ENSURE(!admits(u, 1) && !admits(u, 5));        // still refutes two residues
        ENSURE(admits(u, 6) && admits(u, 8) && admits(u, 9));
        check_sound_binary(len_abs::exact(2).star(), len_abs(), u, false, 30);
        check_sound_binary(len_abs::exact(3).star(), len_abs(), u, false, 30);
    }

    static void tst_meet() {
        len_abs ab_star = len_abs::exact(2).star();              // even
        len_abs a_ba_star = len_abs::exact(1).concat(ab_star);   // odd
        // (ab)* & a(ba)* is empty: disjoint residues certify it
        len_abs m = ab_star.meet(a_ba_star);
        ENSURE(m.residues() == 0 && m.is_empty());
        // meeting two abstractions of the *same* language is sound and can only sharpen.
        // Here a syntactic "even" meets an automaton-style progression 4 + 6N.
        len_abs sharpened = ab_star.meet(len_abs::progression(4, 6));
        for (unsigned n = 0; n <= 60; ++n)
            ENSURE(!admits(sharpened, n) || (admits(ab_star, n) && admits(len_abs::progression(4, 6), n)));
        ENSURE(admits(sharpened, 4) && admits(sharpened, 10));
        // meeting with top changes nothing
        ENSURE(ab_star.meet(len_abs()) == ab_star);
    }

    static void tst_loop_and_opt() {
        len_abs two = len_abs::exact(2);
        ENSURE(two.opt().residues() == 0x1 && two.opt().lo() == 0);
        len_abs odd = len_abs::exact(1).concat(two.star());
        ENSURE(odd.opt().period() == 2 && odd.opt().residues() == 0x3);
        // (a(aa)*){1,2} : odd + odd is even, so lengths 1, 3 (k=1) or 2, 4, 6 (k=2)
        len_abs l12 = odd.loop(1, 2);
        ENSURE(l12.period() == 2 && l12.residues() == 0x3);
        ENSURE(admits(l12, 1) && admits(l12, 2));
        // (aa){1,2} : a fixed-length operand has period 1, so the modulus comes from its gcd
        len_abs f12 = two.loop(1, 2);
        ENSURE(f12.period() == 2 && f12.residues() == 0x1);
        ENSURE(admits(f12, 2) && admits(f12, 4) && !admits(f12, 3));
        // (aaaa){1,3} : multiples of 4 in [4, 12]
        len_abs f13 = len_abs::exact(4).loop(1, 3);
        ENSURE(f13.period() == 4 && f13.residues() == 0x1);
        ENSURE(admits(f13, 4) && admits(f13, 12) && !admits(f13, 6));
        // an unbounded loop falls back on the gcd
        len_abs lu = two.loop(1, UINT_MAX);
        ENSURE(lu.period() == 2 && lu.residues() == 0x1);
        ENSURE(admits(lu, 2) && admits(lu, 4) && !admits(lu, 3));
    }

    static void tst_emptiness_needs_a_full_window() {
        // Residues {1} mod 2 with bounds [2,2] admits nothing.
        len_abs a(2, 2, 2, 0x2);
        ENSURE(a.is_empty());
        // Widening the window to a full period must lose the certificate.
        len_abs b(2, 3, 2, 0x2);
        ENSURE(!b.is_empty());
        // An empty residue mask is empty regardless of the window.
        ENSURE(len_abs(0, UINT_MAX, 4, 0).is_empty());
        // gcd of an empty set is 0, which callers read as "no periodicity to exploit"
        ENSURE(a.gcd() == 0 && a.num_residues() == 0);
    }

    static void tst_residues_mod() {
        len_abs star4 = len_abs::exact(4).star();          // multiples of 4
        ENSURE(star4.residues_mod(2) == 0x1);              // project onto mod 2: even
        ENSURE(star4.residues_mod(8) == ((1ull << 0) | (1ull << 4)));   // lift to mod 8
        // an incompatible modulus has to degrade to "anything"
        ENSURE(star4.residues_mod(3) == 0x7);
        ENSURE(star4.residues_mod(0) == 0);
    }
}

void tst_seq_len_abs() {
    tst_basics();
    tst_progression();
    tst_star_and_plus();
    tst_concat();
    tst_unite_beats_single_progression();
    tst_meet();
    tst_loop_and_opt();
    tst_emptiness_needs_a_full_window();
    tst_residues_mod();
    std::cout << "tst_seq_len_abs: all tests passed\n";
}
