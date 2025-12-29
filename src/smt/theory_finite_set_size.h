
/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_finite_set_size.h

Abstract:

    sub-solver for cardinality constraints of finite sets

--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "util/obj_pair_hashtable.h"
#include "util/union_find.h"
#include "smt/smt_theory.h"
#include "model/finite_set_factory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class theory_finite_set_size {
        struct diseq {
            theory_var x, y;
        };
        struct eq {
            theory_var x, y;
        };
        struct in {
            enode *n;
            bool is_pos;
        };
        using tracking_literal = std::variant<diseq, eq, in>;
        ast_manager          &m;
        context             &ctx;
        theory_finite_set   &th;
        finite_set_util u;
        scoped_ptr<context> m_solver;
        bool m_solver_ran = false;
        ptr_vector<func_decl> m_set_size_decls;
        expr_ref_vector bs;
        obj_map<enode, expr *> n2b;
        obj_map<expr, tracking_literal> m_assumptions;
        expr_ref m_assumption;
        expr_ref_vector m_slacks;
        vector<ptr_vector<expr>> m_slack_members;
        obj_map<expr, app *> m_unique_values;
        app_ref_vector m_pinned;

        void collect_subexpressions(enode_vector& ns);
        void add_def_axioms(enode_vector const &ns);
        void add_singleton_axioms(enode_vector const &ns);
        void add_eq_axioms(enode_vector const &ns);
        void add_diseq_axioms(enode_vector const &ns);
        enode *mk_singleton(enode* n);
        enode *mk_diff(enode *a, enode *b);
        void initialize_solver();

        lbool run_solver();

    public:
        theory_finite_set_size(theory_finite_set &th);
        void add_set_size(func_decl *f);
        lbool final_check(); 
        std::ostream &display(std::ostream &out) const;
        void init_model(model_generator &mg);
        app *get_unique_value(expr *n) {
            return m_unique_values.contains(n) ? m_unique_values[n] : nullptr;
        }
    };
}