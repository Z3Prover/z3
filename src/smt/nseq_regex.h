/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_regex.h

Abstract:

    Lazy regex membership processing for the Nielsen-based string solver.

    Provides Brzozowski derivative computation, ground prefix/suffix
    consumption, cycle detection in derivation histories, and
    stabilizer-based subsumption for regex membership constraints.

    Ports the following ZIPT StrMem operations:
      - SimplifyCharRegex / SimplifyDir (ground prefix/suffix consumption)
      - ExtractCycle / StabilizerFromCycle (cycle detection and widening)
      - TrySubsume (stabilizer-based subsumption)

    The class wraps sgraph operations (brzozowski_deriv, compute_minterms,
    drop_first, etc.) and provides a higher-level interface for
    nielsen_graph and theory_nseq.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"

namespace smt {

    class nseq_regex {
        euf::sgraph& m_sg;

    public:
        nseq_regex(euf::sgraph& sg) : m_sg(sg) {}

        euf::sgraph& sg() { return m_sg; }

        // -----------------------------------------------------------------
        // Basic regex predicates
        // -----------------------------------------------------------------

        // check if regex is the empty language (∅ / re.empty).
        // performs structural analysis beyond is_fail() to detect
        // derived emptiness (e.g., union of empties, concat with empty).
        bool is_empty_regex(euf::snode* re) const;

        // check if regex is the full language (Σ* / re.all)
        bool is_full_regex(euf::snode* re) const {
            return re && re->is_full_seq();
        }

        // check if regex accepts the empty string
        bool is_nullable(euf::snode* re) const {
            return re && re->is_nullable();
        }

        // check if regex is ground (no string variables)
        bool is_ground(euf::snode* re) const {
            return re && re->is_ground();
        }

        // -----------------------------------------------------------------
        // Derivative computation
        // -----------------------------------------------------------------

        // compute Brzozowski derivative of regex w.r.t. character element.
        // returns nullptr on failure.
        euf::snode* derivative(euf::snode* re, euf::snode* elem) {
            return m_sg.brzozowski_deriv(re, elem);
        }

        // compute derivative of a str_mem constraint: advance past one character.
        // the string side is shortened by drop_first and the regex is derived.
        seq::str_mem derive(seq::str_mem const& mem, euf::snode* elem) {
            euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, elem);
            euf::snode* new_str = m_sg.drop_first(mem.m_str);
            return seq::str_mem(new_str, deriv, mem.m_history, mem.m_id, mem.m_dep);
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
        simplify_status simplify_ground_prefix(seq::str_mem& mem);

        // consume ground characters from the back of mem.m_str by computing
        // reverse derivatives. modifies mem in-place.
        // (reverse derivatives require regex reversal; this is a best-effort
        //  simplification that handles the common case of trailing constants.)
        simplify_status simplify_ground_suffix(seq::str_mem& mem);

        // -----------------------------------------------------------------
        // Trivial checks
        // -----------------------------------------------------------------

        // quick check for trivially sat/unsat membership.
        //   returns  1 if satisfied (empty string in nullable regex, or full regex)
        //   returns -1 if conflicting (empty string in non-nullable, or ∅ regex)
        //   returns  0 if undetermined
        int check_trivial(seq::str_mem const& mem) const;

        // -----------------------------------------------------------------
        // Minterm and character computation
        // -----------------------------------------------------------------

        // compute minterms (character class partition) from regex
        void compute_minterms(euf::snode* re, euf::snode_vector& minterms) {
            m_sg.compute_minterms(re, minterms);
        }

        // compute minterms for character splitting, filtering out empty
        // (fail) minterms.  Minterms are regex character-class expressions
        // forming a partition of the alphabet; callers use them to drive
        // fresh-variable creation in character-split modifiers.
        void get_minterms(euf::snode* regex, euf::snode_vector& minterms);

        // collect concrete first-position characters from a regex.
        // extracts characters reachable from to_re leaves and simple ranges.
        void collect_first_chars(euf::snode* re, euf::snode_vector& chars);

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
        bool process_str_mem(seq::str_mem const& mem,
                             vector<seq::str_mem>& out_mems);

        // -----------------------------------------------------------------
        // Cycle detection and stabilizers
        // -----------------------------------------------------------------

        // record current regex in the derivation history of a str_mem.
        // the history tracks a chain of (regex, id) pairs for cycle detection.
        // returns the updated str_mem.
        seq::str_mem record_history(seq::str_mem const& mem, euf::snode* history_re);

        // check if the derivation history of mem contains a cycle, i.e.,
        // the same regex id appears twice in the history chain.
        // if found, returns the cycle entry point regex; nullptr otherwise.
        euf::snode* extract_cycle(seq::str_mem const& mem) const;

        // check if the derivation history exhibits a cycle.
        // returns true when the current regex matches a previously seen regex
        // in the history chain. used to trigger stabilizer introduction.
        bool detect_cycle(seq::str_mem const& mem) const;

        // compute a Kleene star stabilizer from a cycle.
        // given the regex at the cycle point and the current regex,
        // builds r* that over-approximates any number of cycle iterations.
        // returns nullptr if no stabilizer can be computed.
        euf::snode* stabilizer_from_cycle(euf::snode* cycle_regex,
                                          euf::snode* current_regex);

        // try to subsume a str_mem constraint using stabilizer-based
        // reasoning: if extract_cycle finds a cycle, check whether
        // the current regex is already covered by the stabilizer.
        // returns true if the constraint can be dropped.
        bool try_subsume(seq::str_mem const& mem);
    };

}
