/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    sls_fpa_plugin.h

Abstract:

    Theory plugin for floating-point local search

Author:

    Atomic

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/sls/sls_fpa_lookahead.h"
#include "ast/fpa_decl_plugin.h"
#include "ast/rewriter/fpa_rewriter.h"

namespace sls {

    class fpa_plugin : public plugin {
        fpa_util         m_fpa;
        fpa_rewriter     m_rw;
        expr_ref_vector  m_terms;
        expr_ref_vector  m_values;
        fpa_gpu_emulator m_gpu;
        statistics       m_stats;

        [[noreturn]] void not_supported() const;
        expr* value(expr* e) const;
        void cache_value(expr* e, expr* v);
        expr_ref eval(expr* e);
        expr_ref eval_bool(app* e);
        bool contains_fp_term(expr* e) const;
        bool is_fp_atomic_predicate(expr* e) const;
        bool is_fp_predicate(expr* e) const;
        bool assign_var(expr* e, expr* v);
        expr* mk_int_value(sort* s, int value);
        bool try_candidate(expr* var, expr* candidate, expr* goal, bool desired);
        void collect_seed_atoms(expr* e, bool desired, ptr_vector<app>& seeds);
        bool add_candidates_from_atom(app* atom, vector<fpa_lookahead_candidate>& candidates);
        bool repair_predicate_lookahead(app* e, bool desired);
    public:
        fpa_plugin(context& ctx);
        void register_term(expr* e) override;
        expr_ref get_value(expr* e) override;
        void initialize() override;
        void start_propagation() override {}
        void propagate_literal(sat::literal lit) override;
        bool propagate() override;
        bool repair_down(app* e) override;
        void repair_up(app* e) override;
        void repair_literal(sat::literal lit) override;
        bool is_sat() override;
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override;
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override;
    };

}
