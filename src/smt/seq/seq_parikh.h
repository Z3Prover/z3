/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.h

Abstract:

    Parikh image filter for the ZIPT-based Nielsen string solver.

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

    Implements the Parikh filter described in ZIPT
    (https://github.com/CEisenhofer/ZIPT/tree/parikh/ZIPT/Constraints)
    replacing ZIPT's PDD-based Parikh subsolver with Z3's linear arithmetic.

Author:

    Clemens Eisenhofer 2026-03-10
    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "smt/seq/seq_nielsen.h"

namespace seq {

    /**
     * Parikh image filter: generates modular length constraints from
     * regex membership constraints in a nielsen_node.
     *
     * Usage:
     *   seq_parikh parikh(sg);
     *   parikh.apply_to_node(node);      // adds constraints to node
     *
     * Or per-membership:
     *   vector<int_constraint> out;
     *   parikh.generate_parikh_constraints(mem, out);
     */
    class seq_parikh {
        ast_manager& m;
        seq_util     seq;
        arith_util   a;
        th_rewriter  m_rw;
        skolem       m_sk;         // for deterministic, reusable visit-count vars
        unsigned     m_fresh_cnt;  // counter for fresh variable names

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

        // Create a fresh integer variable (name "pk!N") for use as the
        // Parikh multiplier variable k in len(str) = min_len + stride·k.
        expr_ref mk_fresh_int_var();

        // --- exact semi-linear length encoding (visit-count Parikh) ---------
        // Recursively encode the length set of a NON-EXTENDED (classical) regex
        // by introducing, per subterm, an integer "visit-count" variable and
        // Presburger flow constraints (paper "On the Complexity of Equational
        // Horn Clauses", Verma/Seidl/Schwentick).  `count` is the count expr of
        // the current subterm; on success pushes the subterm's structural
        // constraints into `out` and returns its linear length contribution in
        // `contrib`.  Returns false (caller discards) for any operator the flow
        // cannot capture exactly (intersection, complement, diff, xor, of_pred,
        // reverse, derivative, …).
        //
        // Count variables are NOT fresh constants — they are Skolem terms
        //   seq.rc(str_key, root_re, idx)
        // keyed on the membership (str + root regex) and a per-encoding DFS index
        // `idx`.  Re-encoding the same membership therefore reuses the exact same
        // counters instead of leaking new constants on every final_check / node.
        bool rec(expr* re, expr* count, expr* str_key, expr* root_re, unsigned& idx,
                 dep_tracker dep, vector<constraint>& out, expr_ref& contrib);

        // Deterministic non-negative integer count variable
        //   seq.rc(str_key, root_re, idx++)
        // emits c >= 0 into out and bumps idx.
        expr_ref mk_count_var(vector<constraint>& out, dep_tracker dep,
                              expr* str_key, expr* root_re, unsigned& idx);

        // Emit the reachability guard  count = 0 -> c1 = 0.
        void push_zero_guard(vector<constraint>& out, dep_tracker dep, expr* count, expr* c1);

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

        // Apply Parikh constraints to all memberships at a node.
        // Calls generate_parikh_constraints for each str_mem in the node
        // and appends the resulting constraints to node.constraints().
        void apply_to_node(nielsen_node& node);

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
        bool encode_length_set(expr* str_key, expr* re, expr* len_target, dep_tracker dep, vector<constraint>& out);

        // Convert a regex minterm expression to a char_set.
        //
        // A minterm is a Boolean combination of character-class predicates
        // (re.range, re.full_char, complement, intersection) that names a
        // single, indivisible character equivalence class.  Minterms are
        // produced by sgraph::compute_minterms and used in
        // apply_regex_var_split to constrain fresh character variables.
    };

} // namespace seq
