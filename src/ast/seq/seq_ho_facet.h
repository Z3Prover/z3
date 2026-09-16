/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ho_facet.h

Abstract:

    Incremental facet tracking higher-order sequence terms.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/stx_search_tree.h"
#include "util/trail.h"
#include <functional>

namespace seq {

    class ho_facet : public stx::facet_i {
        using add_eq_t = std::function<bool(expr*, expr*)>;
        using find_elaboration_t = std::function<bool(expr*, expr*&)>;

        ast_manager& m;
        seq_util& m_seq;
        seq_rewriter& m_rewriter;
        add_eq_t m_add_eq;
        find_elaboration_t m_find_elaboration;
        app_ref_vector m_terms;
        unsigned m_num_ho_unfolds = 0;
        unsigned m_num_length_axioms = 0;

        bool is_ho_map(expr* term, expr*& f, expr*& i, expr*& s) const {
            f = i = s = nullptr;
            if (!is_app(term))
                return false;
            app* a = to_app(term);
            return m_seq.str.is_map(a, f, s) || m_seq.str.is_mapi(a, f, i, s);
        }

        bool is_ho_term(expr* term, expr*& f, expr*& i, expr*& b, expr*& s) const {
            f = i = b = s = nullptr;
            if (!is_app(term))
                return false;
            app* a = to_app(term);
            return
                is_ho_map(a, f, i, s) ||
                m_seq.str.is_foldl(a, f, b, s) ||
                m_seq.str.is_foldli(a, f, i, b, s);
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
            SASSERT(!m_terms.contains(term));
            m_terms.push_back(static_cast<app*>(term));
            m_trail.push(push_back_vector(m_terms));
        } // namespace seq

        app_ref_vector const& terms() const { return m_terms; }

        bool propagate() {
            unsigned num_terms = m_terms.size();
            bool progress = false;
            for (unsigned i = 0; i < num_terms; ++i) {
                app* term = m_terms.get(i);
                expr* f = nullptr, *s = nullptr, *b = nullptr, *idx = nullptr;
                VERIFY(is_ho_term(term, f, idx, b, s));

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
                if (status != BR_FAILED && m_add_eq(ho_elaboration, rewritten)) {
                    ++m_num_ho_unfolds;
                    progress = true;
                }
            }

            for (unsigned i = 0; i < num_terms; ++i) {
                app* term = m_terms.get(i);
                expr* f = nullptr, *s = nullptr, *idx = nullptr;
                if (!is_ho_map(term, f, idx, s))
                    continue;
                expr_ref len_map(m_seq.str.mk_length(term), m);
                expr_ref len_s(m_seq.str.mk_length(s), m);
                if (m_add_eq(len_map, len_s)) {
                    ++m_num_length_axioms;
                    progress = true;
                }
            }
            return progress;
        }

        unsigned num_ho_unfolds() const { return m_num_ho_unfolds; }
        unsigned num_length_axioms() const { return m_num_length_axioms; }

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
            f->m_num_ho_unfolds = m_num_ho_unfolds;
            f->m_num_length_axioms = m_num_length_axioms;
            return f;
        }

        bool is_satisfied() const override { return true; }

        std::ostream& display(std::ostream& out) const override {
            out << "ho_facet: " << m_terms.size() << " term(s)\n";
            for (expr* term : m_terms)
                out << "  " << mk_pp(term, m) << "\n";
            return out;
        }
    };

}
