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
      the regex. For example, if RegEx is (aa)*, it asserts (seq.len S) = 2*X_s
      where X_s >= 0 is a fresh integer variable.
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

        // Extract semi-linear length constraint for a regex.
        // Returns true if a useful constraint can be extracted.
        // If so, sets:
        //   period > 0: lengths are of the form (base + period*k), k >= 0
        //   period == 0: length is exactly base
        bool get_length_constraint(expr* r, unsigned& base, unsigned& period) const;

        // Helper: internalize and get literal for an expr.
        literal mk_literal(expr* e);

        // Helper: assert a clause (disjunction of literals).
        void assert_axiom(literal_vector& lits);

    public:
        theory_seq_len(context& ctx);
    };

}
