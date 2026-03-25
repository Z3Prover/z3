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
        bool check_parikh_conflict(nielsen_node& node);

        // Compute the length stride of a regex expression.
        // Exposed for testing and external callers.
        unsigned get_length_stride(expr* re) { return compute_length_stride(re); }

        // Convert a regex minterm expression to a char_set.
        //
        // A minterm is a Boolean combination of character-class predicates
        // (re.range, re.full_char, complement, intersection) that names a
        // single, indivisible character equivalence class.  Minterms are
        // produced by sgraph::compute_minterms and used in
        // apply_regex_var_split to constrain fresh character variables.
    };

} // namespace seq
