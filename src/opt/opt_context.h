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
#include "opt_solver.h"
#include "optsmt.h"
#include "maxsmt.h"
#include "objective_ast.h"

namespace opt {

    class opt_solver;

    class context {
        typedef map<symbol, maxsmt*, symbol_hash_proc, symbol_eq_proc> map_t;
        ast_manager&        m;
        expr_ref_vector     m_hard_constraints;
        ref<opt_solver>     m_solver;
        params_ref          m_params;
        optsmt              m_optsmt;
        map_t               m_maxsmts;
        expr_ref_vector     m_objs;
        svector<bool>       m_ismaxs;
    public:
        context(ast_manager& m);
        ~context();
        void add_soft_constraint(expr* f, rational const& w, symbol const& id);
        void add_objective(app* t, bool is_max) { m_objs.push_back(t); m_ismaxs.push_back(is_max); }
        void add_hard_constraint(expr* f) { m_hard_constraints.push_back(f);  }

        lbool execute(objective & obj, bool committed);
        lbool execute_min_max(min_max_objective & obj, bool committed);
        lbool execute_maxsat(maxsat_objective & obj, bool committed);
        lbool execute_lex(compound_objective & obj);
        lbool execute_box(compound_objective & obj);
        lbool execute_pareto(compound_objective & obj);

        lbool optimize();
        void set_cancel(bool f);
        void reset_cancel() { set_cancel(false); }
        void cancel() { set_cancel(true); }
        void collect_statistics(statistics& stats) const;
        void display_assignment(std::ostream& out);
        void display_range_assignment(std::ostream& out);
        static void collect_param_descrs(param_descrs & r);
        void updt_params(params_ref& p);
    private:
        void validate_feasibility(maxsmt& ms);
    };

}

#endif
