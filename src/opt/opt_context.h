/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.h

Abstract:
    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    TODO:

    - type check objective term and assertions. It should pass basic sanity being
      integer, real (, bit-vector) or other supported objective function type.

    - add appropriate statistics tracking to opt::context

--*/
#ifndef _OPT_CONTEXT_H_
#define _OPT_CONTEXT_H_

#include "ast.h"
#include "solver.h"

namespace opt {

    class context {
        ast_manager& m;
        expr_ref_vector m_hard_constraints;
        expr_ref_vector  m_soft_constraints;
        vector<rational> m_weights;

        expr_ref_vector m_objectives;
        svector<bool>   m_is_max;
        ref<solver>     m_solver;

    public:
        context(ast_manager& m):
            m(m),
            m_hard_constraints(m),
            m_soft_constraints(m),
            m_objectives(m)
        {}

        void add_soft_constraint(expr* f, rational const& w) {
            m_soft_constraints.push_back(f);
            m_weights.push_back(w);
        }

        void add_objective(expr* t, bool is_max) {
            m_objectives.push_back(t);
            m_is_max.push_back(is_max);
        }

        void add_hard_constraint(expr* f) {
            m_hard_constraints.push_back(f);
        }

        void set_solver(solver* s) {
            m_solver = s;
        }

        void optimize();

        void cancel();
        void reset_cancel();

    private:
        bool is_maxsat_problem() const;

    };

}

#endif
