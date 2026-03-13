/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    theory_seq_len.h

Abstract:

    Theory solver for sequence length constraints.

    Handles the theory of sequences (seq_decl_plugin) using partial axiom
    instantiation:
    - Axiomatizes (seq.len S) >= 0 for all sequence variables S.
    - Derives stronger lower/upper bounds on seq.len based on the structure of S.
    - Axiomatizes S in RegEx by extracting semi-linear length constraints from
      the regex and asserting them into the arithmetic solver.
    - The semi-linear set of valid lengths is represented as a finite union
      (disjunction) of arithmetic progressions.  Each progression is expressed
      as an existential linear constraint:
        ∃ k_0,...,k_{n-1} ≥ 0 :  |s| = base + ∑ periods[i] * k_i
      For unions the disjunction is encoded via fresh guard Boolean variables.
      For concatenations the Minkowski sum is computed by merging period lists.
    - Returns FC_DONE in final_check (incomplete but sound partial solver).

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-10

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "model/seq_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_model_generator.h"

namespace smt {

    class theory_seq_len : public theory {
        seq_util        m_util;
        arith_util      m_autil;

        // -----------------------------------------------------------------------
        // Semi-linear length constraint representation
        //
        // A single "arm" represents one arithmetic progression of valid lengths:
        //   ∃ k_0,...,k_{n-1} ≥ 0 : |s| = base + ∑ periods[i] * k_i
        //
        // When periods is empty the constraint collapses to |s| = base (fixed).
        // When periods has one entry p it is  |s| = base + k*p,  k ≥ 0
        //   (same as: |s| ≥ base  ∧  |s| mod p = base mod p).
        // Multiple entries arise from Minkowski sums of concat sub-regexes.
        //
        // A complete semi-linear set is a disjunction of arms:
        //   the string length satisfies at least one arm.
        // -----------------------------------------------------------------------
        struct len_arm {
            unsigned          base    = 0;
            svector<unsigned> periods;          // coefficients for fresh k_i vars
        };
        using len_arms = svector<len_arm>;

        // Maximum number of arms we are willing to maintain.  Limits the
        // Minkowski-product explosion when concatenating two multi-arm regexes.
        static const unsigned MAX_LEN_ARMS = 16;

        // -----------------------------------------------------------------------
        // Virtual overrides required by theory base class
        // -----------------------------------------------------------------------
        bool internalize_atom(app* atom, bool gate_ctx) override;
        bool internalize_term(app* term) override;
        void new_eq_eh(theory_var, theory_var) override {}
        void new_diseq_eh(theory_var, theory_var) override {}
        theory* mk_fresh(context* new_ctx) override;
        char const* get_name() const override { return "seq-len"; }
        void display(std::ostream& out) const override;

        // -----------------------------------------------------------------------
        // Optional overrides
        // -----------------------------------------------------------------------
        void assign_eh(bool_var v, bool is_true) override;
        final_check_status final_check_eh(unsigned) override { return FC_DONE; }
        void push_scope_eh() override { theory::push_scope_eh(); }
        void pop_scope_eh(unsigned num_scopes) override { theory::pop_scope_eh(num_scopes); }
        void init_model(model_generator& mg) override;

        // -----------------------------------------------------------------------
        // Axiom generation helpers
        // -----------------------------------------------------------------------

        // Assert (seq.len e) >= 0.
        void add_length_non_neg(expr* e);

        // Assert length axioms implied by S in R (when the membership is true).
        // lit is the literal for (S in R).
        void add_regex_length_axioms(expr* s, expr* r, literal lit);

        // Returns true if the regex r has a fixed length (min==max).
        bool has_fixed_length(expr* r, unsigned& len) const;

        // Compute the semi-linear set of valid lengths for r.
        // Returns an empty vector when no useful constraint can be extracted
        // (e.g. r matches strings of arbitrary length or the structure is
        // too complex to analyze).
        len_arms get_length_arms(expr* r) const;

        // Assert constraints for one progression arm under a guard literal.
        //   cond_lit → ∃ k_i ≥ 0 : |s| = arm.base + ∑ arm.periods[i] * k_i
        // Fresh Int constants are introduced for each k_i.
        void assert_one_arm(expr* s, literal cond_lit, const len_arm& arm);

        // Assert the disjunction of length arms:
        //   mem_lit → (arm_0 holds) ∨ (arm_1 holds) ∨ ...
        // For a single arm the constraint is asserted directly under mem_lit.
        // For multiple arms, fresh guard Booleans are introduced as selectors.
        void assert_len_arms(expr* s, literal mem_lit, const len_arms& arms);

        // Helper: internalize and get literal for an expr.
        literal mk_literal(expr* e);

        // Helper: assert a clause (disjunction of literals).
        void assert_axiom(literal_vector& lits);

    public:
        theory_seq_len(context& ctx);
    };

}
