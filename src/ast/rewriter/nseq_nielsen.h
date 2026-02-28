/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    nseq_nielsen.h

Abstract:

    Nielsen transformation-based word equation solver.
    Self-contained rewriter utility for decomposing and solving
    word equations using Nielsen transformations.

    Given a word equation lhs_1·...·lhs_n = rhs_1·...·rhs_m,
    the solver applies:
    - Constant matching: strip matching constants from both sides
    - Empty elimination: x = ε
    - Variable splitting: x·α = c·β → x = c·x' or x = ε
    - Length-based reasoning for pruning

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"

namespace seq {

    // Result of a Nielsen transformation step
    enum class nielsen_result {
        solved,       // equation is trivially satisfied
        conflict,     // equation is unsatisfiable
        reduced,      // equation was simplified
        split,        // case split needed
        unchanged     // no progress
    };

    // A case split produced by Nielsen transformation.
    // Represents a substitution x -> t and the resulting simplified equation.
    struct nielsen_branch {
        expr_ref       var;         // variable being assigned
        expr_ref       term;        // value assigned (ε, constant prefix + fresh var, etc.)
        expr_ref_vector new_lhs;    // resulting LHS after substitution
        expr_ref_vector new_rhs;    // resulting RHS after substitution
        nielsen_branch(ast_manager& m) : var(m), term(m), new_lhs(m), new_rhs(m) {}
    };

    // Nielsen transformation engine for word equations.
    // Self-contained, no dependency on SMT context.
    class nielsen {
        ast_manager&    m;
        seq_util        m_util;
        arith_util      m_autil;
        seq_rewriter&   m_rw;

        // Scratch space
        expr_ref_vector m_lhs, m_rhs;

        // Strip matching constants/units from both sides of an equation.
        // Returns true if anything was stripped.
        bool strip_common_prefix(expr_ref_vector& lhs, expr_ref_vector& rhs);
        bool strip_common_suffix(expr_ref_vector& lhs, expr_ref_vector& rhs);

        // Check if an expression is a unit (single character)
        bool is_unit(expr* e) const;

        // Check if an expression is the empty string
        bool is_empty(expr* e) const;

        // Check if an expression vector contains any variables
        bool has_var(expr_ref_vector const& es) const;

        // Apply substitution x -> t in an expression vector
        void apply_subst(expr* var, expr* term, expr_ref_vector const& src, expr_ref_vector& dst);

        // Decompose multi-character string constants into individual character units
        bool decompose_strings(expr_ref_vector& es);

    public:
        nielsen(ast_manager& m, seq_rewriter& rw);

        // Check if an expression is a string variable (not unit, not constant)
        bool is_var(expr* e) const;

        // Main simplification: reduce a word equation as far as possible
        // without case splitting. Returns the result status.
        //   lhs, rhs: in/out - the equation sides (decomposed into concat components)
        nielsen_result simplify(expr_ref_vector& lhs, expr_ref_vector& rhs);

        // Generate case split branches for a word equation that cannot
        // be further simplified. The equation should be in simplified form.
        //   branches: output - possible branches to explore
        // Returns false if no splits are possible (stuck).
        bool split(expr_ref_vector const& lhs, expr_ref_vector const& rhs,
                   vector<nielsen_branch>& branches);

        // Check if an equation is trivially solved (both sides empty)
        bool is_solved(expr_ref_vector const& lhs, expr_ref_vector const& rhs) const;

        // Check for conflict (mismatched constants)
        bool is_conflict(expr_ref_vector const& lhs, expr_ref_vector const& rhs) const;
    };
}
