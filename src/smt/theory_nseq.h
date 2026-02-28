/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_nseq.h

Abstract:

    Theory solver for strings based on Nielsen transformations
    and lazy regex membership (ZIPT algorithm).

Author:

    Clemens Eisenhofer
    Nikolaj Bjorner (nbjorner) 2025-2-28

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/seq_factory.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/smt_model_generator.h"

namespace smt {

    class theory_nseq : public theory {
        seq_util         m_util;
        arith_util       m_autil;
        seq_rewriter     m_seq_rewrite;
        th_rewriter      m_rewrite;
        seq::skolem      m_sk;
        arith_value      m_arith_value;
        bool             m_has_seq;

        final_check_status final_check_eh(unsigned) override;
        bool internalize_atom(app* atom, bool) override;
        bool internalize_term(app*) override;
        void internalize_eq_eh(app* atom, bool_var v) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        void assign_eh(bool_var v, bool is_true) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        void relevant_eh(app* n) override;
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_nseq, *new_ctx); }
        char const* get_name() const override { return "nseq"; }
        void display(std::ostream& out) const override;
        void collect_statistics(::statistics& st) const override;
        model_value_proc* mk_value(enode* n, model_generator& mg) override;
        void init_model(model_generator& mg) override;
        void finalize_model(model_generator& mg) override;
        theory_var mk_var(enode* n) override;
        void apply_sort_cnstr(enode* n, sort* s) override;

    public:
        theory_nseq(context& ctx);
        ~theory_nseq() override;
        void init() override;
    };
}
