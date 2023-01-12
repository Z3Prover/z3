/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    euf_completion.h

Abstract:

    Ground completion for equalities

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-30

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/euf/euf_egraph.h"
#include "ast/rewriter/th_rewriter.h"

namespace euf {

    class completion : public dependent_expr_simplifier {

        struct stats {
            unsigned m_num_rewrites = 0;
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        egraph                 m_egraph;
        enode*                 m_tt, *m_ff;
        ptr_vector<expr>       m_todo;
        enode_vector           m_args, m_reps, m_nodes_to_canonize;
        expr_ref_vector        m_canonical, m_eargs;
        expr_dependency_ref_vector m_deps;
        unsigned               m_epoch = 0;
        unsigned_vector        m_epochs;
        th_rewriter            m_rewriter;
        stats                  m_stats;
        bool                   m_has_new_eq = false;

        enode* mk_enode(expr* e);
        bool is_new_eq(expr* a, expr* b);
        void update_has_new_eq(expr* g);
        expr_ref mk_and(expr* a, expr* b);
        void add_egraph();
        void map_canonical();
        void read_egraph();
        expr_ref canonize(expr* f, expr_dependency_ref& dep);
        expr_ref canonize_fml(expr* f, expr_dependency_ref& dep);
        expr* get_canonical(expr* f, expr_dependency_ref& d);
        expr* get_canonical(enode* n);
        void set_canonical(enode* n, expr* e);
        expr_dependency* explain_eq(enode* a, enode* b);
        expr_dependency* explain_conflict();
    public:
        completion(ast_manager& m, dependent_expr_state& fmls);
        char const* name() const override { return "euf-reduce"; }
        void push() override { m_egraph.push(); dependent_expr_simplifier::push(); }
        void pop(unsigned n) override { dependent_expr_simplifier::pop(n); m_egraph.pop(n); }
        void reduce() override;
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override { m_stats.reset(); }
    };
}
