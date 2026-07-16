/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex.h

Abstract:

    Lazy regex membership processing for the Nielsen-based string solver.

    Provides Brzozowski derivative computation, ground prefix/suffix
    consumption, BFS emptiness/intersection checks, and minterm/char-set
    utilities for regex membership constraints.

    Cycle detection and stabilizer-based subsumption live in the landing
    decomposition and land-state views of nielsen_graph (seq_nielsen.cpp);
    the legacy stabilizer store that used to reside here has been removed.

    The class wraps sgraph operations (brzozowski_deriv, compute_minterms,
    drop_first, etc.) and provides a higher-level interface for
    nielsen_graph and theory_nseq.

Author:

    Clemens Eisenhofer 2026-03-01
    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include "util/uint_set.h"
#include "util/lbool.h"

namespace seq {

    class seq_regex {
        ast_manager &m;
        seq_util &seq;
        euf::sgraph& m_sg;

        // cache for emptiness check (snode id -> lbool)
        u_map<lbool> m_empty_cache;

        // -----------------------------------------------------------------
        // BFS emptiness check helpers (private)
        // -----------------------------------------------------------------

        // Collect character boundary points from range predicates and
        // to_re string literals in a regex. Boundaries partition the
        // alphabet into equivalence classes where all characters in
        // the same class produce identical derivatives.
        void collect_char_boundaries(euf::snode const* re, unsigned_vector& bounds) const;

        // Build a set of representative character snodes, one per
        // alphabet equivalence class, derived from the boundary points
        // of the given regex.
        bool get_alphabet_representatives(euf::snode const* re, euf::snode_vector& reps);

    public:

        // Convert a regex minterm expression to a char_set.
        // Used to transform symbolic boundaries (re.range, re.complement, etc.)
        // into exact character sets (char_set).
        //
        // Supported expressions:
        //   re.full_char       → full set [0, max_char]
        //   re.range(lo, hi)   → char_set [lo, hi] (inclusive on both ends)
        //   re.complement(r)   → complement of minterm_to_char_set(r)
        //   re.inter(r1, r2)   → intersection of both sets
        //   re.diff(r1, r2)    → r1 minus r2  (= r1 ∩ complement(r2))
        //   re.to_re(unit(c))  → singleton {c}
        //   re.empty           → empty set
        //   anything else      → full set (conservative, sound over-approximation)
        // -----------------------------------------------------------------------
        // minterm → char_set conversion
        // -----------------------------------------------------------------------
        char_set minterm_to_char_set(expr* minterm_re);

        seq_regex(euf::sgraph& sg) : m(sg.get_manager()), seq(sg.get_seq_util()), m_sg(sg) {}

        euf::sgraph& sg() { return m_sg; }

        // -----------------------------------------------------------------
        // Basic regex predicates
        // -----------------------------------------------------------------

        // check if regex is the empty language (∅ / re.empty).
        // performs structural analysis beyond is_fail() to detect
        // derived emptiness (e.g., union of empties, concat with empty).
        bool is_empty_regex(euf::snode const* re) const;

        // BFS emptiness check over the Brzozowski derivative automaton.
        // Explores reachable derivative states using representative
        // characters from each alphabet equivalence class.
        //   l_true  — regex is definitely empty (no accepting states reachable)
        //   l_false — regex is definitely non-empty (found a nullable state)
        //   l_undef — inconclusive (hit exploration bound or failed derivative)
        // max_states caps the number of explored states to prevent blowup.
        lbool is_empty_bfs(euf::snode const* re, unsigned max_states = 10000);

        // Check emptiness of the intersection of multiple regexes.
        // Uses BFS over the product of Brzozowski derivative automata.
        //   l_true  — intersection is definitely empty
        //   l_false — intersection is definitely non-empty
        //   l_undef — inconclusive (hit exploration bound)
        lbool check_intersection_emptiness(euf::snode_vector const& regexes, unsigned max_states = UINT_MAX);

        // Length of a SHORTEST word in L(re): level-order BFS over the
        // Brzozowski derivative automaton (contrast is_empty_bfs, whose
        // worklist is LIFO and therefore finds *some* accepting state, not
        // the nearest one).
        //   l_true  — found; len = length of a shortest accepting word
        //   l_false — language is definitely empty (within budget)
        //   l_undef — inconclusive (exploration bound / unsupported shape)
        lbool shortest_word_length(euf::snode const* re, unsigned& len, unsigned max_states = 10000);

        // check if regex is the full language (Σ* / re.all)
        static bool is_full_regex(euf::snode const* re) {
            return re && re->is_full_seq();
        }

        // check if regex accepts the empty string
        // (projection-aware: re may contain re.proj operators)
        bool is_nullable(euf::snode const* re) const {
            return re && m_sg.re_nullable(re) == l_true;
        }

        // check if regex is ground (no string variables)
        bool is_ground(euf::snode const* re) const {
            return re && re->is_ground();
        }

        // -----------------------------------------------------------------
        // Derivative computation
        // -----------------------------------------------------------------

        // compute Brzozowski derivative of regex w.r.t. character element.
        // returns nullptr on failure.
        euf::snode const* derivative(euf::snode const* re, euf::snode const* elem) {
            return m_sg.brzozowski_deriv(re, elem);
        }

        // check if all minterms of the regex produce the same Brzozowski
        // derivative ("uniform derivative").  When this holds, the derivative
        // is independent of the character value: for any character c,
        // deriv(regex, c) = result.  This enables deterministic consumption
        // of symbolic (variable) characters without branching.
        // Returns the uniform derivative if found, nullptr otherwise.
        euf::snode const* try_uniform_derivative(euf::snode const* regex) const;

        // compute derivative of a str_mem constraint: advance past one character.
        // the string side is shortened by drop_first and the regex is derived.
        str_mem derive(str_mem const& mem, euf::snode const* elem) {
            euf::snode const* deriv = m_sg.brzozowski_deriv(mem.m_regex, elem);
            euf::snode const* new_str = m_sg.drop_first(mem.m_str);
            return str_mem(mem.m, new_str, deriv, mem.m_dep);
        }

        // -----------------------------------------------------------------
        // Ground prefix/suffix consumption
        // -----------------------------------------------------------------

        enum class simplify_status { ok, conflict, satisfied };

        // consume ground characters from the front of mem.m_str by computing
        // Brzozowski derivatives against mem.m_regex.
        // stops when:
        //   - the string front is not a concrete character (ok)
        //   - a derivative produces ∅ (conflict)
        //   - the string becomes empty and regex is nullable (satisfied)
        //   - the string becomes empty and regex is not nullable (conflict)
        // modifies mem in-place.
        simplify_status simplify_ground_prefix(str_mem& mem);

        // consume ground characters from the back of mem.m_str by computing
        // reverse derivatives. modifies mem in-place.
        // (reverse derivatives require regex reversal; this is a best-effort
        //  simplification that handles the common case of trailing constants.)
        simplify_status simplify_ground_suffix(str_mem& mem);

        // -----------------------------------------------------------------
        // Trivial checks
        // -----------------------------------------------------------------

        // quick check for trivially sat/unsat membership.
        //   returns  1 if satisfied (empty string in nullable regex, or full regex)
        //   returns -1 if conflicting (empty string in non-nullable, or ∅ regex)
        //   returns  0 if undetermined
        int check_trivial(str_mem const& mem) const;

        // -----------------------------------------------------------------
        // Minterm and character computation
        // -----------------------------------------------------------------

        // compute minterms (character class partition) from regex
        void compute_minterms(euf::snode const* re, euf::snode_vector& minterms) {
            m_sg.compute_minterms(re, minterms);
        }

        // compute minterms for character splitting, filtering out empty
        // (fail) minterms.  Minterms are regex character-class expressions
        // forming a partition of the alphabet; callers use them to drive
        // fresh-variable creation in character-split modifiers.
        void get_minterms(euf::snode const* regex, euf::snode_vector& minterms);

        // collect concrete first-position characters from a regex.
        // extracts characters reachable from to_re leaves and simple ranges.
                // -----------------------------------------------------------------
        // Membership processing
        // -----------------------------------------------------------------

        // process a str_mem constraint by consuming ground characters from
        // the string front via Brzozowski derivatives.  If the entire ground
        // prefix is consumed and the constraint is neither satisfied nor
        // conflicting, the (simplified) constraint is pushed to out_mems
        // for the Nielsen graph to expand via character-split modifiers.
        // returns false if the constraint is immediately conflicting
        // (empty string in non-nullable regex, or derivative yields ∅).
        bool process_str_mem(str_mem const& mem,
                             vector<str_mem>& out_mems);
    };

}
