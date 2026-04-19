
/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    fold_unfold.h

Abstract:

    fold-unfold simplifier

Author:

    Nikolaj Bjorner (nbjorner) 2025-11-5.

--*/

#pragma once

#include "util/scoped_ptr_vector.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/simplifiers/extract_eqs.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    class fold_unfold : public dependent_expr_simplifier {
        friend class solve_context_eqs;

        struct stats {
            unsigned m_num_steps = 0;
            unsigned m_num_elim_vars = 0;
            void reset() {
                m_num_steps = 0;
                m_num_elim_vars = 0;
            }
        };

        struct config {
            bool m_enabled = true;
        };

        stats m_stats;
        config m_config;
        th_rewriter m_rewriter;
        egraph m_egraph;
        scoped_ptr_vector<extract_eq> m_extract_plugins;
        unsigned_vector m_var2id;               // app->get_id() |-> small numeral
        scoped_ptr<expr_substitution> m_subst;  // current substitution
        vector<std::pair<proof_ref, expr_dependency *>> m_pr_dep;

        void get_eqs(dep_eq_vector &eqs);
        void extract_subst(bool fuf, dep_eq_vector const &eqs);
        void insert_subst(expr *v, expr *t, expr_dependency* d);
        void apply_subst(vector<dependent_expr> &old_fmls);
        void reduce_alias(bool fuf);
        void reduce_linear();

        size_t *to_ptr(size_t i) const {
            return reinterpret_cast<size_t *>(i);
        }
        unsigned from_ptr(size_t *s) const {
            return (unsigned)reinterpret_cast<size_t>(s);
        }
        unsigned push_pr_dep(proof *pr, expr_dependency *d);
        expr_dependency *explain_eq(enode *a, enode *b);

        ptr_vector<expr> m_todo;
        enode_vector m_args, m_find;
        unsigned_vector m_node2level;
        enode_vector m_level2node;
        unsigned m_level_count = 0;

        void set_levels();
        void set_level(enode *n);
        bool is_linear_term(enode *n);
        
        unsigned m_generation = 0;
        unsigned m_th_var = 0;
        enode *mk_enode(expr *e);

        void fold(expr *e, expr_ref &result, proof_ref &pr);
        void unfold(unsigned n, enode *e, expr_dependency* d, vector<std::pair<expr_ref, expr_dependency *>> &es);
        void unfold_arg(unsigned n, unsigned i, enode *e, expr_ref_vector &args, expr_dependency *d,
                        vector<std::pair<expr_ref, expr_dependency *>> &es);

    public:
        fold_unfold(ast_manager &m, dependent_expr_state &fmls);

        char const *name() const override {
            return "fold-unfold";
        }

        void reduce() override;

        void updt_params(params_ref const &p) override;

        void collect_param_descrs(param_descrs &r) override;

        void collect_statistics(statistics &st) const override;

        void reset_statistics() override {
            m_stats.reset();
        }
    };
}  // namespace euf
