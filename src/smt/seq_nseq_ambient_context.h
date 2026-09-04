/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_nseq_ambient_context.h

Abstract:

    Concrete `ambient_context_i` (ast/seq/seq_ambient_context.h) backed by a
    live `smt::theory_nseq` instance. Structurally mirrors
    `seq::theory_seq_ambient_context` (smt/seq_ambient_context.h), but wraps
    `theory_nseq` instead of `theory_seq`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "ast/seq/seq_ambient_context.h"
#include "ast/seq/seq_eq_facet.h"
#include "smt/theory_nseq.h"

namespace seq {

    class theory_nseq_ambient_context : public ambient_context_i<eq_tree::dep_tracker> {
        smt::theory_nseq& m_th;
    public:
        explicit theory_nseq_ambient_context(smt::theory_nseq& th)
            : ambient_context_i<eq_tree::dep_tracker>(th.get_manager(), th.m_seq), m_th(th) {}

        bool lower_bound(expr* e, rational& lo, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            return m_th.lower_bound(e, lo);
        }

        bool upper_bound(expr* e, rational& hi, eq_tree::dep_tracker& dep) override {
            dep = nullptr;
            return m_th.upper_bound(e, hi);
        }

        bool current_value(expr* e, rational& v) override {
            return m_th.get_num_value(e, v);
        }

        eq_tree::dep_tracker literal_if_false(expr*) override {
            // Not currently exposed by theory_nseq; conservatively unknown.
            return nullptr;
        }

        void add_diseq_axiom(expr*, expr*) override {
            // No-op: no standalone axiom-injection entry point distinct from
            // theory_nseq's ordinary disequality propagation.
        }
    };

} // namespace seq
