/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ho_facet.h

Abstract:

    Incremental facet tracking higher-order sequence terms: `seq.map`,
    `seq.mapi`, `seq.foldl`, and `seq.foldli` applications. Each applies a
    function pointwise (map/mapi) or as a left-to-right accumulation
    (foldl/foldli) over a sequence argument `s` whose own structure is
    frequently still symbolic when the term needs reasoning about, so it
    cannot simply be rewritten away term-by-term the way a plain arithmetic
    or Boolean operator can.

    Two independent unfolding strategies, tried in order of increasing cost:

      - `propagate()` is the cheap, syntactic path. It first asks the
        rewriter to reduce the term directly (works once `s` is fully
        ground). If that fails, it asks an external `find_elaboration`
        callback for some other term already known equal to `s` that *is*
        concrete - found by walking `s`'s own e-graph congruence class, not
        by searching the model - retries the rewrite against that
        elaborated form, and, if it now succeeds, records the result
        conditioned on `s = elaboration` actually holding. It also asserts
        the one structural fact that needs no unfolding at all:
        `len(map(f,s)) = len(s)` (ditto mapi).

      - `propagate_model()` is the fallback for when no syntactic
        elaboration is available at all. It asks the ambient arithmetic
        model for a concrete *length* of `s` (bounded to 256, to keep the
        unfolding tractable), builds an explicit index-by-index shape
        `seq.unit(nth(s,0)) ++ ... ++ seq.unit(nth(s,n-1))` purely from that
        length, substitutes it into the term, and rewrites. Since map/foldl
        are themselves defined as recursive functions over the sequence
        structure, this can still leave behind unresolved recursive calls;
        the subsequent loop manually expands non-recursive step bodies
        (bounded to `n+1` rounds, enough to fully unroll a chain of `n`
        steps) until nothing further changes. The resulting fact is only
        sound conditioned on the observed length actually being `n`
        (`length(s) = n` is just this branch's current model, not a
        guaranteed invariant), so it is asserted as a guarded implication,
        never an unconditional equality.

    `publish` controls how far a `propagate_model()` discovery travels:
    `sf.add_constraint(...)` always happens, strengthening only the current
    node's own backend; `m_add_eq(...)` additionally broadcasts the guarded
    equality as a general fact when `publish` is true. The per-node
    `ho_propagation` plugin below always passes `publish=false` (DFS
    refinement stays branch-local - today's model-observed length may not
    survive backtracking); the dedicated root-level call in theory_nseq's
    final-check uses the default `publish=true`, since a length refined
    before the search even starts is a safer global commitment.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/seq/seq_solver_facet_i.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <functional>

namespace seq {

    class ho_facet : public stx::facet_i {
        // A non-null premise guards an equality obtained from an input elaboration.
        using add_eq_t = std::function<bool(expr*, expr*, expr*)>;
        using find_elaboration_t = std::function<bool(expr*, expr*&)>;

        ast_manager& m;
        seq_util& m_seq;
        seq_rewriter& m_rewriter;
        add_eq_t m_add_eq;
        find_elaboration_t m_find_elaboration;
        app_ref_vector m_terms;
        obj_hashtable<expr> m_unfolded;
        unsigned m_num_ho_unfolds = 0;
        unsigned m_num_length_axioms = 0;

        bool is_ho_map(expr* term, expr*& f, expr*& i, expr*& s) const {
            f = i = s = nullptr;
            return m_seq.str.is_map(term, f, s) || m_seq.str.is_mapi(term, f, i, s);
        }

        bool is_ho_fold(expr* term, expr*& f, expr*& i, expr*& b, expr*& s) const {
            f = i = b = s = nullptr;
            return m_seq.str.is_foldl(term, f, b, s) || m_seq.str.is_foldli(term, f, i, b, s);
        }


        bool is_ho_term(expr* term, expr*& f, expr*& i, expr*& b, expr*& s) const {
            f = i = b = s = nullptr;
            return is_ho_map(term, f, i, s) || is_ho_fold(term, f, i, b, s);
        }

    public:
        ho_facet(
            trail_stack& trail,
            ast_manager& m,
            seq_util& seq,
            seq_rewriter& rewriter,
            add_eq_t add_eq,
            find_elaboration_t find_elaboration) :
            facet_i(trail),
            m(m),
            m_seq(seq),
            m_rewriter(rewriter),
            m_add_eq(std::move(add_eq)),
            m_find_elaboration(std::move(find_elaboration)),
            m_terms(m) {}

        ast_manager& get_manager() const { return m; }

        bool is_ho_term(expr* term, expr*& s) const {
            expr* f = nullptr, *i = nullptr, *b = nullptr;
            return is_ho_term(term, f, i, b, s);
        }

        void add_term(expr* term) {
            SASSERT(is_app(term));
            SASSERT(!m_terms.contains(to_app(term)));
            m_terms.push_back(static_cast<app*>(term));
            m_trail.push(push_back_vector(m_terms));
        } // namespace seq

        app_ref_vector const& terms() const { return m_terms; }

        bool is_unfolded(app* term) const { return m_unfolded.contains(term); }

        bool propagate_lengths() {
            unsigned num_terms = m_terms.size();
            bool progress = false;
            for (unsigned i = 0; i < num_terms; ++i) {
                app* term = m_terms.get(i);
                expr* f = nullptr, *s = nullptr, *idx = nullptr;
                if (!is_ho_map(term, f, idx, s))
                    continue;
                expr_ref len_map(m_seq.str.mk_length(term), m);
                expr_ref len_s(m_seq.str.mk_length(s), m);
                if (m_add_eq(len_map, len_s, nullptr)) {
                    ++m_num_length_axioms;
                    progress = true;
                }
            }
            return progress;
        }

        bool propagate() {
            unsigned num_terms = m_terms.size();
            bool progress = false;
            for (unsigned i = 0; i < num_terms; ++i) {
                app* term = m_terms.get(i);
                if (is_unfolded(term))
                    continue;
                expr* f = nullptr, *s = nullptr, *b = nullptr, *idx = nullptr;
                VERIFY(is_ho_term(term, f, idx, b, s));

                expr_ref eager_rewritten(m);
                br_status eager_status = m_rewriter.mk_app_core(
                    term->get_decl(),
                    term->get_num_args(),
                    term->get_args(),
                    eager_rewritten);
                if (eager_status != BR_FAILED) {
                    if (m_add_eq(term, eager_rewritten, nullptr))
                        ++m_num_ho_unfolds;
                    m_unfolded.insert(term);
                    m_trail.push(insert_obj_trail<expr>(m_unfolded, term));
                    progress = true;
                    continue;
                }

                expr* elaboration = nullptr;
                if (!m_find_elaboration(s, elaboration))
                    continue;

                app_ref ho_elaboration(m);
                if (m_seq.str.is_map(term))
                    ho_elaboration = m_seq.str.mk_map(f, elaboration);
                else if (m_seq.str.is_mapi(term))
                    ho_elaboration = m_seq.str.mk_mapi(f, idx, elaboration);
                else if (m_seq.str.is_foldl(term))
                    ho_elaboration = m_seq.str.mk_foldl(f, b, elaboration);
                else
                    ho_elaboration = m_seq.str.mk_foldli(f, idx, b, elaboration);

                expr_ref rewritten(m);
                br_status status = m_rewriter.mk_app_core(
                    ho_elaboration->get_decl(),
                    ho_elaboration->get_num_args(),
                    ho_elaboration->get_args(),
                    rewritten);
                if (status != BR_FAILED) {
                    expr_ref premise(m.mk_eq(s, elaboration), m);
                    if (m_add_eq(term, rewritten, premise))
                        ++m_num_ho_unfolds;
                    m_unfolded.insert(term);
                    m_trail.push(insert_obj_trail<expr>(m_unfolded, term));
                    progress = true;
                }
            }

            progress |= propagate_lengths();
            return progress;
        }

        unsigned num_ho_unfolds() const { return m_num_ho_unfolds; }
        unsigned num_length_axioms() const { return m_num_length_axioms; }

        // DFS refinement stays branch-local; only root refinement publishes SMT axioms.
        bool propagate_model(solver_facet_i& sf, bool publish = true) {
            if (m_terms.empty())
                return false;
            bool progress = false;
            th_rewriter rw(m);
            unsigned num_terms = m_terms.size();
            for (unsigned j = 0; j < num_terms; ++j) {
                app_ref term(m_terms.get(j), m);
                if (is_unfolded(term))
                    continue;
                expr* f = nullptr, *s = nullptr, *b = nullptr, *idx = nullptr;
                VERIFY(is_ho_term(term, f, idx, b, s));
                expr_ref length(m_seq.str.mk_length(s), m);
                rw(length);
                rational n;
                if (!sf.value(length, n) || !n.is_unsigned() || n > rational(256))
                    continue;
                expr_ref_vector units(m);
                for (unsigned k = 0; k < n.get_unsigned(); ++k) {
                    expr_ref index(sf.get_arith_util().mk_int(k), m);
                    expr_ref element(m_seq.str.mk_nth_i(s, index), m);
                    units.push_back(m_seq.str.mk_unit(element));
                }
                expr_ref shape(m_seq.str.mk_concat(units, s->get_sort()), m);
                expr_ref_vector args(m);
                for (expr* arg : *term)
                    args.push_back(arg);
                args.set(args.size() - 1, shape);
                expr_ref result(m.mk_app(term->get_decl(), args.size(), args.data()), m);
                rw(result);
                recfun::util rec(m);
                var_subst instantiate(m);
                // Expand nonrecursive step bodies even when their elements are symbolic.
                for (unsigned k = 0; k <= n.get_unsigned(); ++k) {
                    expr_safe_replace macros(m);
                    bool changed = false;
                    for (expr* t : subterms_postorder::ground(result)) {
                        if (!rec.is_defined(t) || !rec.has_def(to_app(t)->get_decl()))
                            continue;
                        auto const& d = rec.get_def(to_app(t)->get_decl());
                        if (!d.is_fun_macro() || !d.get_rhs() || rec.contains_def(d.get_rhs()))
                            continue;
                        expr_ref body(instantiate(d.get_rhs(), to_app(t)->get_num_args(), to_app(t)->get_args()), m);
                        macros.insert(t, body);
                        changed = true;
                    }
                    if (!changed)
                        break;
                    macros(result);
                    rw(result);
                }
                expr_ref numeral(sf.get_arith_util().mk_numeral(n, true), m);
                expr_ref lower(sf.get_arith_util().mk_ge(length, numeral), m);
                expr_ref upper(sf.get_arith_util().mk_le(length, numeral), m);
                expr_ref guard(m.mk_and(lower, upper), m);
                expr_ref definition(m.mk_implies(guard, m.mk_eq(term, result)), m);
                proof_ref definition_proof(m);
                if (m.proofs_enabled())
                    definition_proof = m_seq.mk_proof(symbol("seq-ho-unfold"), 0, nullptr, definition);
                if (sf.add_constraint(definition, nullptr, definition_proof, symbol("seq-ho-unfold"))) {
                    if (publish)
                        m_add_eq(term, result, guard);
                    progress = true;
                }
                expr_ref shape_axiom(m.mk_implies(guard, m.mk_eq(s, shape)), m);
                proof_ref shape_proof(m);
                if (m.proofs_enabled())
                    shape_proof = m_seq.mk_proof(symbol("seq-ho-input"), 0, nullptr, shape_axiom);
                if (sf.add_constraint(shape_axiom, nullptr, shape_proof, symbol("seq-ho-input"))) {
                    if (publish)
                        m_add_eq(s, shape, guard);
                    progress = true;
                }
            }
            return progress;
        }

        facet_i* clone(trail_stack& trail) const override {
            ho_facet* f = alloc(
                ho_facet,
                trail,
                m,
                m_seq,
                m_rewriter,
                m_add_eq,
                m_find_elaboration);
            f->m_terms.append(m_terms);
            for (expr* term : m_unfolded)
                f->m_unfolded.insert(term);
            f->m_num_ho_unfolds = m_num_ho_unfolds;
            f->m_num_length_axioms = m_num_length_axioms;
            return f;
        }

        bool is_satisfied() const override { return m_unfolded.size() == m_terms.size(); }

        std::ostream& display(std::ostream& out) const override {
            out << "ho_facet: " << m_terms.size() << " term(s)\n";
            for (expr* term : m_terms)
                out << "  " << mk_pp(term, m) << "\n";
            return out;
        }
    };

    class ho_propagation : public eq_tree::propagation_plugin_i {
    public:
        char const* name() const override { return "ho-propagate"; }
        // Always publish=false (see module comment): this runs at every
        // DFS node, so a model-observed length here is only ever a
        // branch-local hint, not a fact to broadcast globally.
        stx::simplify_result propagate(eq_tree::node& n) override {
            auto ac = get_ambient(n);
            auto& hf = ac.context().ho_facet(n);
            return hf.propagate_model(ac.solver_facet_ref(), false) ?
                stx::simplify_result::proceed : stx::simplify_result::noop;
        }
    };

}
