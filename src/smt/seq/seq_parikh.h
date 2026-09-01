/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.h

Abstract:

    Parikh image filter for the Nielsen string solver.

    Implements Parikh-based arithmetic constraint generation for
    nielsen_node instances.  For a regex membership constraint str ∈ r,
    the Parikh image of r constrains the multiset of characters in str.
    This module computes the "length stride" (period) of the length
    language of r and generates modular arithmetic constraints of the form

        len(str) = min_len + stride · k    (k ≥ 0, k fresh integer)

    which tighten the arithmetic subproblem beyond plain min/max bounds,
    where concrete variable bounds are queried from the arithmetic subsolver.

    For example:
      • str ∈ (ab)*  → min_len = 0, stride = 2  → len(str) = 2·k
      • str ∈ a(bc)* → min_len = 1, stride = 2  → len(str) = 1 + 2·k
      • str ∈ ab|abc → stride = 1 (no useful modular constraint)

    The generated int_constraints are added to the node's integer constraint
    set and discharged by the integer subsolver (see seq_nielsen.h,
    simple_solver).

Author:

    Clemens Eisenhofer 2026-03-10
    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_parikh.h"
#include "ast/rewriter/seq_profile_abs.h"
#include "smt/seq/seq_nielsen.h"

namespace seq {

    /**
     * Parikh image filter: generates modular length constraints from
     * regex membership constraints in a nielsen_node.
     *
     * Usage (per-membership):
     *   seq_parikh parikh(sg);
     *   vector<int_constraint> out;
     *   parikh.generate_parikh_constraints(mem, out);
     */
    class seq_parikh {
        ast_manager& m;
        seq_util     seq;
        arith_util   a;
        parikh       m_pk;         // consolidated per-membership modular length constraints

        // The per-letter profile abstraction (see regex_residues below).  It
        // is free of solver state; this class only chooses the letters and
        // assembles the congruence rows.
        seq::profile_abs m_abs;

        // Compute the stride (period) of the length language of a regex.
        //
        // The stride k satisfies: all lengths in L(re) are congruent to
        // min_length(re) modulo k.  A stride of 1 means every integer
        // length is possible (no useful modular constraint).  A stride of
        // 0 is a sentinel meaning the language is empty or has a single
        // fixed length (already captured by bounds).
        //
        // Examples:
        //   stride(to_re("ab"))   = 0  (fixed length 2)
        //   stride((ab)*)         = 2  (lengths 0, 2, 4, ...)
        //   stride((abc)*)        = 3  (lengths 0, 3, 6, ...)
        //   stride(a*b*)          = 1  (all lengths possible)
        //   stride((ab)*(cd)*)    = 2  (lengths 0, 2, 4, ...)
        //   stride((ab)*|(abc)*)  = 1  (lengths 0, 2, 3, 4, ...)
        unsigned compute_length_stride(expr* re);

        // Collect the concrete characters of a node with their multiplicities,
        // most frequent first, capped at `max_letters`.
        void collect_letters(nielsen_node const& node, unsigned max_letters,
                             unsigned_vector& letters);

    public:
        explicit seq_parikh(euf::sgraph& sg);

        // Generate Parikh modular length constraints for one membership.
        //
        // When stride > 1 and min_len < max_len (bounds don't pin length exactly,
        // and the language is non-empty):
        //   adds: len(str) = min_len + stride · k   (equality)
        //         k ≥ 0                              (non-negativity)
        //         k ≤ (max_len - min_len) / stride   (upper bound, when max_len bounded)
        // These tighten the integer constraint set for the subsolver.
        // Dependencies are copied from mem.m_dep.
        // Does nothing when min_len ≥ max_len (empty or fixed-length language).
        void generate_parikh_constraints(str_mem const& mem,
                                         vector<constraint>& out);

        // Quick Parikh feasibility check (no solver call).
        //
        // For each single-variable membership str ∈ re, checks whether the
        // modular constraint  len(str) = min_len + stride · k  (k >= 0)
        // has any solution given the current per-variable bounds obtained via
        // node.var_lb(str) and node.var_ub(str).
        //
        // Returns true when a conflict is detected (no valid k exists for
        // some membership).  The caller should then mark the node with
        // backtrack_reason::parikh_image.
        //
        // This is a lightweight pre-check that avoids calling the integer
        // subsolver.  It is sound (never returns true for a satisfiable node)
        // but incomplete (may miss conflicts that require the full solver).
        str_mem const* check_parikh_conflict(nielsen_node& node, dep_tracker& dep);

        // Compute the length stride of a regex expression.
        // Exposed for testing and external callers.
        unsigned get_length_stride(expr* re) { return compute_length_stride(re); }

        // Exact semi-linear length encoding for a regex membership.
        //
        // For a NON-EXTENDED (classical) regex R, encodes the *exact* set
        //   { |w| : w ∈ L(R) }
        // as an existential Presburger formula over fresh visit-count variables,
        // asserting  len_target = Σ (char-leaf counts)  together with the
        // per-subterm flow constraints (concat: equal child counts; union:
        // count = c1 + c2; star/plus/loop: bounded body count with the
        // reachability guard count=0 → body=0).  This is linear in |R| and,
        // unlike the single gcd `stride`, does not collapse on unions — e.g.
        // (aa)*|(aaa)* yields len = 2·c1 + 3·c2 with c1+c2 the active branch,
        // i.e. exactly {2k} ∪ {3k}.
        //
        // Returns true and appends the encoding (all carrying `dep`) to `out`
        // when R is classical; returns false (leaving `out` unchanged) for
        // extended regexes (intersection / complement / diff / of_pred / …),
        // in which case the caller keeps the coarse interval/stride fallback.
        //
        // `str_key` identifies the membership's string term (mem.m_str): together
        // with `re` it keys the reusable Skolem count variables, so re-encoding
        // the same membership does not allocate new counters.
        //
        // Delegates to the consolidated, nielsen_node/str_mem-free implementation
        // in ast/rewriter/seq_parikh (seq::parikh::encode_length_set), re-tagging
        // each produced assertion with `dep`.  `len_target` must equal
        // seq.str.mk_length(str_key): every call site already constructs it that
        // way, and the delegate computes it internally rather than taking it as
        // a parameter.
        bool encode_length_set(expr* str_key, expr* re, expr* len_target, dep_tracker dep, vector<constraint>& out);

        // Convert a regex minterm expression to a char_set.
        //
        // A minterm is a Boolean combination of character-class predicates
        // (re.range, re.full_char, complement, intersection) that names a
        // single, indivisible character equivalence class.  Minterms are
        // produced by sgraph::compute_minterms and used in
        // apply_regex_var_split to constrain fresh character variables.

        // --- per-letter Parikh abstraction, refined by length ---------------
        //
        // The module above abstracts a regex by the LENGTHS of its words.  The
        // routines below abstract it by the number of occurrences of a single
        // character, taken modulo a small number -- the (k=1, n=m) observer, or
        // equivalently the classic Parikh image projected on one letter.
        //
        // Profile domain: a word w is abstracted to the pair
        //
        //     (#sigma(w) mod modulus,  min(|w|, 2))
        //
        // and a language to the SET of profiles of its words, held as a bitmask
        // with bit (c * 3 + l) set when profile (c, l) is possible.  The
        // abstraction over-approximates: w in L implies profile(w) is in the
        // mask, so an empty intersection with what an equation forces refutes.
        //
        // The length component is what makes EXTENDED regexes usable.  A pure
        // count abstraction cannot see through complement -- comp(R) has to go
        // to the full set, since a word and its permutations share a count --
        // so the common idiom
        //
        //     (re.inter re.allchar (re.comp (str.to_re "a")))   "any char but a"
        //
        // collapses to "anything at all".  Tracking length pins re.allchar to
        // length exactly 1, and the complement of a ONE-CHARACTER language can
        // then be excluded exactly at that length, recovering "one non-sigma
        // character".  Without it the abstraction is vacuous on precisely the
        // benchmarks it is meant for.
        //
        // Returns the residues of #sigma, i.e. the profile mask projected on the
        // count axis, as a bitmask over Z_modulus.  All bits set carries no
        // information.  `modulus` must lie in [2, max_modulus].
        unsigned regex_residues(expr* re, unsigned modulus, unsigned sigma);

        // Largest modulus the profile bitmask can hold (3 length classes per
        // residue must fit in an unsigned).
        static const unsigned max_modulus = seq::profile_abs::max_modulus;

        // Per-letter congruence refutation over a whole node.  No branching, no
        // substitution and no solver call, in the spirit of check_parikh_conflict.
        //
        // A membership  w in L  gives  #sigma(w) mod m  in regex_residues(L), and
        // w is a concatenation of tokens, so this is a linear congruence in the
        // unknowns n[x] = #sigma(x) >= 0.  An equation  l = r  gives the exact
        // congruence  #sigma(l) = #sigma(r).  Together they form one system per
        // (sigma, m); an infeasible system refutes the node outright.
        //
        // sigma ranges over the most frequent concrete characters occurring in
        // the node and m over [2, max_mod].  Every choice is independently sound,
        // so searching only adds power.  Tokens that are not fully concrete are
        // opaque non-negative unknowns keyed by snode id -- sound for any token,
        // since equal snodes denote equal strings; it only weakens the test.
        //
        // Returns true when some system is infeasible, and then sets `dep` to the
        // join of the dependencies of the rows that were used.
        bool check_letter_conflict(nielsen_node const& node, dep_tracker& dep,
                                   unsigned max_mod, unsigned max_letters);
    };

} // namespace seq
