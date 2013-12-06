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

namespace opt {

    class opt_solver;

    class context {
        typedef map<symbol, maxsmt*, symbol_hash_proc, symbol_eq_proc> map_t;
        typedef map<symbol, unsigned, symbol_hash_proc, symbol_eq_proc> map_id;
        enum objective_t {
            O_MAXIMIZE,
            O_MINIMIZE,
            O_MAXSMT
        };
        struct objective {
            objective_t m_type;
            app_ref     m_term; // for maximize, minimize
            symbol      m_id;   // for maxsmt
            unsigned    m_index;
            objective(bool is_max, app_ref& t, unsigned idx):
                m_type(is_max?O_MAXIMIZE:O_MINIMIZE),
                m_term(t),
                m_id(),
                m_index(idx)
            {}
            objective(ast_manager& m, symbol id):
                m_type(O_MAXSMT),
                m_term(m),
                m_id(id),
                m_index(0)
            {}
        };
        ast_manager&        m;
        expr_ref_vector     m_hard_constraints;
        ref<opt_solver>     m_solver;
        params_ref          m_params;
        optsmt              m_optsmt;        
        map_t               m_maxsmts;
        map_id              m_indices;
        vector<objective>   m_objectives;
        model_ref           m_model;
    public:
        context(ast_manager& m);
        ~context();
        unsigned add_soft_constraint(expr* f, rational const& w, symbol const& id);
        unsigned add_objective(app* t, bool is_max);
        void add_hard_constraint(expr* f) { m_hard_constraints.push_back(f);  }

        lbool optimize();

        void get_model(model_ref& m);

        void set_cancel(bool f);
        void reset_cancel() { set_cancel(false); }
        void cancel() { set_cancel(true); }
        void collect_statistics(statistics& stats) const;
        void display_assignment(std::ostream& out);
        void display_range_assignment(std::ostream& out);
        static void collect_param_descrs(param_descrs & r);
        void updt_params(params_ref& p);

        expr_ref get_lower(unsigned idx);
        expr_ref get_upper(unsigned idx);

    private:
        void validate_feasibility(maxsmt& ms);

        lbool execute(objective const& obj, bool committed);
        lbool execute_min_max(unsigned index, bool committed, bool is_max);
        lbool execute_maxsat(symbol const& s, bool committed);
        lbool execute_lex();
        lbool execute_box();
        lbool execute_pareto();
        expr_ref to_expr(inf_eps const& n);

        void push();
        void pop(unsigned sz);
        opt_solver& get_solver();

    };

}

#endif
