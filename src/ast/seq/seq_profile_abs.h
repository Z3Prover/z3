/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_profile_abs.h

Abstract:

    Per-letter Parikh abstraction of a regular expression, refined by length.

    A word w is abstracted to the pair

        (#sigma(w) mod modulus,  min(|w|, 2))

    and a language to the SET of profiles of its words, held as a bitmask with
    bit (c * 3 + l) set when profile (c, l) is possible.  The abstraction
    over-approximates: w in L implies profile(w) is in the mask, so an empty
    intersection with what an equation forces refutes.

    The length component is what makes EXTENDED regexes usable.  A pure count
    abstraction cannot see through complement -- comp(R) has to go to the full
    set, since a word and its permutations share a count -- so the common idiom

        (re.inter re.allchar (re.comp (str.to_re "a")))   "any char but a"

    collapses to "anything at all".  Tracking length pins re.allchar to length
    exactly 1, and the complement of a ONE-CHARACTER language can then be
    excluded exactly at that length, recovering "one non-sigma character".

    This module is deliberately free of any solver state: it maps an AST regex
    to a bitmask and nothing else, so it can be driven by any string solver.
    The consumer supplies the letters and the constraint rows.

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "util/obj_hashtable.h"

namespace seq {

    class profile_abs {
        seq_util seq;

        // state of the pass: a "pass" is one choice of (sigma, modulus), over
        // which the caches below stay valid.
        unsigned m_pk_mod    = 0;   // modulus of the abstraction being computed
        unsigned m_pk_sigma  = 0;   // character being counted
        unsigned m_pk_top    = 0;   // full profile mask for m_pk_mod
        unsigned m_pk_budget = 0;   // remaining recursion steps, 0 = exhausted
        obj_map<expr, unsigned> m_pk_prof;    // memo for profiles()
        obj_map<expr, unsigned> m_pk_forced;  // memo for forced()

        unsigned prof_cat(unsigned a, unsigned b) const;
        unsigned prof_pow(unsigned a, unsigned n) const;
        unsigned prof_star(unsigned a) const;
        unsigned prof_loop(unsigned a, unsigned lo, unsigned hi) const;
        unsigned prof_chars(bool has_sigma, bool has_other) const;

    public:
        explicit profile_abs(ast_manager& m) : seq(m) {}

        // Largest modulus the profile bitmask can hold (3 length classes per
        // residue must fit in an unsigned).
        static const unsigned max_modulus = 10;

        // Begin a pass for one (modulus, sigma) choice; resets the memos.
        void begin_pass(unsigned modulus, unsigned sigma);

        // Over-approximation of the profiles of L(re): w in L(re) implies
        // profile(w) is in the result.  Degrades to the full mask when a
        // construct is out of scope or the budget runs out -- always sound.
        unsigned profiles(expr* re);

        // Under-approximation of the profiles p for which EVERY word with
        // profile p lies in L(re).  Makes complement precise: no word of
        // comp(re) can have such a profile.  Degrades to the empty set.
        unsigned forced(expr* re);

        // Residues of #sigma, i.e. the profile mask projected on the count
        // axis, as a bitmask over Z_modulus.  All bits set carries no
        // information.  `modulus` must lie in [2, max_modulus].
        unsigned regex_residues(expr* re, unsigned modulus, unsigned sigma);

        // Same projection, but within a pass already begun by begin_pass.
        // Lets a caller abstract several regexes under one (sigma, modulus)
        // choice while sharing the memo tables.
        unsigned residues_in_pass(expr* re);
    };

} // namespace seq
