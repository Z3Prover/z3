/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    theory_ff.h

Abstract:

    Ground theory combination for prime fields using modular algebra and
    model arrangements, with an exact bounded bit-vector representation
    when algebra is inconclusive. Original field sorts/terms stay in the
    equality engine, so arrays, datatypes and uninterpreted functions
    retain their original signatures.

Author:

    Romain Soulat

--*/
#pragma once

#include "smt/smt_theory.h"
#include "math/ff/ff_polynomial.h"
#include "ast/ff_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/ff_bv_operations.h"
#include "util/obj_pair_hashtable.h"
#include <memory>

namespace smt {
    struct ff_encoding_cache;
    // Ground theory combination using modular algebra and model arrangements,
    // with an exact bounded BV representation when algebra is inconclusive.
    // Original field sorts/terms stay in the equality engine, so arrays,
    // datatypes and uninterpreted functions retain their original signatures.
    class theory_ff : public theory {
        ff_util ff;
        bv_util bv;
        th_rewriter rw;
        ff_bv_operations operations;
        func_decl_ref_vector helpers;
        obj_map<sort, func_decl *> wraps, unwraps;
        obj_hashtable<func_decl> decoders;
        unsigned axioms = 0;
        unsigned native_checks = 0, native_conflicts = 0, arrangements = 0, fallbacks = 0;
        unsigned root_clauses = 0;
        obj_hashtable<sort> bv_fields; // fallback is local to a field, never the whole context
        void refresh_bv_fields();
        ff::basis_cache memo;
        obj_map<sort, std::unique_ptr<ff_encoding_cache>> encodings;
        obj_hashtable<expr> constrained;
        // Deduplicates root-splitting by the merged terms' original operands,
        // which are already kept alive by their enodes.
        obj_pair_hashtable<expr, expr> split_atoms;
        obj_map<expr, expr *> root_norm;   // bounded pure-rewriting cache; cleared on pop
        expr_ref_vector root_norm_pins;
        obj_map<expr, rational> native_values;
        expr_ref_vector model_values;
        // Interface equalities/disequalities between this theory's variables,
        // accumulated incrementally from new_eq_eh/new_diseq_eh and popped on
        // backtracking (see ctx.push_trail/push_back_vector below).
        svector<std::pair<theory_var, theory_var>> new_eqs, new_diseqs;

        void ensure_helpers(sort *s);
        expr_ref wrap(expr *e);
        void assert_axiom(expr *e, bool simplify = true);
        void constrain(expr *e);
        expr_ref square_root_term(expr *e);
        bool propagate_roots();
        final_check_status check_native();
        final_check_status final_check_eh(unsigned) override;
        void pop_scope_eh(unsigned n) override;
        void reset_eh() override;
        void init_search_eh() override {
            // A canceled internalization may have stopped halfway through a
            // bridge definition. Retry all live definitions on the next check.
            constrained.reset();
            split_atoms.reset();
            refresh_bv_fields();
        }

        bool internalize_atom(app *, bool) override {
            return false;
        }
        bool internalize_term(app *e) override;
        void apply_sort_cnstr(enode *n, sort *s) override;
        void relevant_eh(expr *e) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void init_model(model_generator &mg) override;
        model_value_proc *mk_value(enode *n, model_generator &mg) override;
        void finalize_model(model_generator &mg) override;

    public:
        explicit theory_ff(context &ctx);
        ~theory_ff() override;
        theory *mk_fresh(context *ctx) override {
            return alloc(theory_ff, *ctx);
        }
        char const *get_name() const override {
            return "finite-field";
        }
        void display(std::ostream &out) const override {
            display_var2enode(out);
        }
        void collect_statistics(::statistics &st) const override {
            st.update("ff combination axioms", axioms);
            st.update("ff native checks", native_checks);
            st.update("ff native conflicts", native_conflicts);
            st.update("ff arrangements", arrangements);
            st.update("ff bv fallbacks", fallbacks);
            st.update("ff root clauses", root_clauses);
            st.update("ff normalization cache entries", root_norm_pins.size() / 2);
            st.update("ff basis cache hits", memo.hits);
            st.update("ff basis cache misses", memo.misses);
        }
    };
}  // namespace smt
