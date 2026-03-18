/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_regex.h

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
        euf::sgraph& m_sg;

        // -----------------------------------------------------------------
        // Stabilizer store (non-backtrackable, persists across solve() calls)
        // Mirrors ZIPT Environment.stabilizers / selfStabilizing
        // (Environment.cs:36-37)
        // -----------------------------------------------------------------

        // Maps regex snode id → list of stabilizer snodes.
        // Each regex may accumulate multiple stabilizers from different
        // cycle detections. The list is deduplicated by pointer equality.
        u_map<ptr_vector<euf::snode>> m_stabilizers;

        // Set of regex snode ids that are self-stabilizing, i.e., the
        // stabilizer for the regex is the regex itself (e.g., r*).
        // Mirrors ZIPT Environment.selfStabilizing (Environment.cs:37)
        uint_set                      m_self_stabilizing;

        // -----------------------------------------------------------------
        // BFS emptiness check helpers (private)
        // -----------------------------------------------------------------

        // Collect character boundary points from range predicates and
        // to_re string literals in a regex. Boundaries partition the
        // alphabet into equivalence classes where all characters in
        // the same class produce identical derivatives.
        void collect_char_boundaries(euf::snode* re, unsigned_vector& bounds) const;

        // Build a set of representative character snodes, one per
        // alphabet equivalence class, derived from the boundary points
        // of the given regex.
        void get_alphabet_representatives(euf::snode* re, euf::snode_vector& reps);

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
        char_set minterm_to_char_set(expr* minterm_re);

        seq_regex(euf::sgraph& sg) : m_sg(sg) {}

        euf::sgraph& sg() { return m_sg; }

        // -----------------------------------------------------------------
        // Stabilizer store API
        // Mirrors ZIPT Environment stabilizer management
        // (Environment.cs:114-146)
        // -----------------------------------------------------------------

        // Reset all stabilizer data. Called at the start of each solve()
        // invocation if fresh stabilizer state is desired.
        // Note: stabilizers persist across depth-bound iterations by default;
        // only call this to clear accumulated state.
        void reset_stabilizers();

        // Add a stabilizer for a regex. De-duplicates by pointer equality.
        // Mirrors ZIPT Environment.AddStabilizer (Environment.cs:114-123).
        void add_stabilizer(euf::snode* regex, euf::snode* stabilizer);

        // Get the union of all stabilizers registered for a regex.
        // Returns a single re.union snode combining all stabilizers,
        // or nullptr if no stabilizers exist for the regex.
        // Mirrors ZIPT Environment.GetStabilizerUnion (Environment.cs:125-128).
        euf::snode* get_stabilizer_union(euf::snode* regex);

        // Check if any stabilizers have been registered for a regex.
        bool has_stabilizers(euf::snode* regex) const;

        // Get raw stabilizer list for a regex (read-only).
        // Returns nullptr if no stabilizers exist.
        ptr_vector<euf::snode> const* get_stabilizers(euf::snode* regex) const;

        // Mark a regex as self-stabilizing (stabilizer == regex itself).
        // Mirrors ZIPT Environment.SetSelfStabilizing (Environment.cs:143-146).
        void set_self_stabilizing(euf::snode* regex);

        // Check if a regex is marked as self-stabilizing.
        // Mirrors ZIPT Environment.IsSelfStabilizing (Environment.cs:134-141).
        bool is_self_stabilizing(euf::snode* regex) const;

        // -----------------------------------------------------------------
        // Self-stabilizing auto-detection and propagation through derivatives
        // -----------------------------------------------------------------

        // Determine if a regex is inherently self-stabilizing based on its
        // structure. Returns true for:
        //   - R* (Kleene star): D(c, R*) = D(c,R)·R*, so R* is its own
        //     stabilizer regardless of the character.
        //   - Σ* (full_seq): D(c, Σ*) = Σ*, trivially self-stabilizing.
        //   - ∅  (fail/empty language): no live derivatives, trivially stable.
        //   - Complement of full_seq (~Σ* = ∅): also trivially stable.
        // Does NOT mark the snode; call set_self_stabilizing to persist.
        bool compute_self_stabilizing(euf::snode* regex) const;

        // After computing a derivative of parent, propagate the self-
        // stabilizing flag to the derivative result if warranted.
        // Applies structural rules:
        //   - If parent is R* → derivative is always self-stabilizing
        //     (derivative has the form D(c,R)·R* which contains the R* tail).
        //   - If parent is R·S and S is self-stabilizing → derivative may
        //     inherit from the self-stabilizing tail.
        //   - If parent is R|S and both are self-stabilizing → derivative is.
        //   - If parent is R∩S and both are self-stabilizing → derivative is.
        //   - If parent is ~R and R is self-stabilizing → derivative is.
        // Updates the internal self-stabilizing set for the derivative.
        void propagate_self_stabilizing(euf::snode* parent, euf::snode* deriv);

        // Convenience: compute derivative and propagate self-stabilizing flags.
        // Equivalent to calling derivative() followed by
        // propagate_self_stabilizing().
        euf::snode* derivative_with_propagation(euf::snode* re, euf::snode* elem);

        // -----------------------------------------------------------------
        // Basic regex predicates
        // -----------------------------------------------------------------

        // check if regex is the empty language (∅ / re.empty).
        // performs structural analysis beyond is_fail() to detect
        // derived emptiness (e.g., union of empties, concat with empty).
        bool is_empty_regex(euf::snode* re) const;

        // BFS emptiness check over the Brzozowski derivative automaton.
        // Explores reachable derivative states using representative
        // characters from each alphabet equivalence class.
        //   l_true  — regex is definitely empty (no accepting states reachable)
        //   l_false — regex is definitely non-empty (found a nullable state)
        //   l_undef — inconclusive (hit exploration bound or failed derivative)
        // max_states caps the number of explored states to prevent blowup.
        lbool is_empty_bfs(euf::snode* re, unsigned max_states = 10000);

        // Check emptiness of the intersection of multiple regexes.
        // Uses BFS over the product of Brzozowski derivative automata.
        //   l_true  — intersection is definitely empty
        //   l_false — intersection is definitely non-empty
        //   l_undef — inconclusive (hit exploration bound)
        // Mirrors ZIPT NielsenNode.CheckEmptiness (NielsenNode.cs:1429-1469)
        lbool check_intersection_emptiness(ptr_vector<euf::snode> const& regexes,
                                           unsigned max_states = 10000);

        // Check if L(subset_re) ⊆ L(superset_re).
        // Computed as: subset_re ∩ complement(superset_re) = ∅.
        // Mirrors ZIPT NielsenNode.IsLanguageSubset (NielsenNode.cs:1382-1385)
        lbool is_language_subset(euf::snode* subset_re, euf::snode* superset_re);

        // Collect all primitive regex constraints on variable `var` from
        // the node's str_mem list and return their intersection as a
        // single regex snode (using re.inter).
        // Returns nullptr if no primitive constraints found.
        euf::snode* collect_primitive_regex_intersection(
            euf::snode* var, seq::nielsen_node const& node);

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

        // check if all minterms of the regex produce the same Brzozowski
        // derivative ("uniform derivative").  When this holds, the derivative
        // is independent of the character value: for any character c,
        // deriv(regex, c) = result.  This enables deterministic consumption
        // of symbolic (variable) characters without branching.
        // Returns the uniform derivative if found, nullptr otherwise.
        // Mirrors ZIPT's SimplifyCharRegex uniform-derivative fast path.
        euf::snode* try_uniform_derivative(euf::snode* regex);

        // compute derivative of a str_mem constraint: advance past one character.
        // the string side is shortened by drop_first and the regex is derived.
        // Propagates self-stabilizing flags from the parent regex to the derivative.
        seq::str_mem derive(seq::str_mem const& mem, euf::snode* elem) {
            euf::snode* parent_re = mem.m_regex;
            euf::snode* deriv = m_sg.brzozowski_deriv(parent_re, elem);
            if (deriv)
                propagate_self_stabilizing(parent_re, deriv);
            euf::snode* new_str = m_sg.drop_first(mem.m_str);
            return seq::str_mem(new_str, deriv, mem.m_lit, mem.m_history, mem.m_id, mem.m_dep);
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

        // Strengthened stabilizer construction with sub-cycle detection.
        // Replays the consumed character tokens from cycle_history on the
        // cycle regex, detecting sub-cycles (where the derivative loops
        // back to the original regex). For each sub-cycle, builds a
        // stabilizer from the interleaved character tokens and filtered
        // sub-stabilizers.
        // Returns a union of all sub-cycle stabilizer bodies, or nullptr
        // if no non-trivial stabilizer can be built.
        // Mirrors ZIPT StrMem.StabilizerFromCycle (StrMem.cs:163-225).
        euf::snode* strengthened_stabilizer(euf::snode* cycle_regex,
                                            euf::snode* cycle_history);

        // Get filtered stabilizer star: for regex state re, retrieve
        // existing stabilizers, filter out those whose language can
        // start with any character in excluded_char, and wrap the
        // remaining in star(union(...)).
        // Returns nullptr (or empty-equivalent) if no valid stabilizers.
        // Mirrors ZIPT StrMem.GetFilteredStabilizerStar (StrMem.cs:228-243).
        euf::snode* get_filtered_stabilizer_star(euf::snode* re,
                                                  euf::snode* excluded_char);

        // Extract the cycle portion of a str_mem's history by comparing
        // the current history with an ancestor's history length.
        // Returns the sub-sequence of tokens consumed since the ancestor,
        // or nullptr if the history did not advance.
        euf::snode* extract_cycle_history(seq::str_mem const& current,
                                           seq::str_mem const& ancestor);

        // try to subsume a str_mem constraint using stabilizer-based
        // reasoning. Enhanced version: checks if the leading variable's
        // language (intersection of all its primitive regex constraints)
        // is a subset of star(union(stabilizers)) for the current regex.
        // Falls back to cycle-based pointer equality check.
        // returns true if the constraint can be dropped.
        // Mirrors ZIPT StrMem.TrySubsume (StrMem.cs:354-386).
        bool try_subsume(seq::str_mem const& mem, seq::nielsen_node const& node);
    };

}
