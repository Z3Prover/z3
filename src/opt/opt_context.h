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
#include "model_converter.h"

namespace opt {

    class opt_solver;

    class context {
        struct free_func_visitor;
        typedef map<symbol, maxsmt*, symbol_hash_proc, symbol_eq_proc> map_t;
        typedef map<symbol, unsigned, symbol_hash_proc, symbol_eq_proc> map_id;
        typedef vector<std::pair<inf_eps, inf_eps> > bounds_t;
        enum objective_t {
            O_MAXIMIZE,
            O_MINIMIZE,
            O_MAXSMT
        };

        struct objective {
            objective_t m_type;
            app_ref     m_term;          // for maximize, minimize term
            expr_ref_vector   m_terms;   // for maxsmt
            vector<rational>  m_weights; // for maxsmt
            rational          m_offset;  // for maxsmt
            bool              m_neg;     // negate
            symbol      m_id;            // for maxsmt
            unsigned    m_index;         // for maximize/minimize index

            objective(bool is_max, app_ref& t, unsigned idx):
                m_type(is_max?O_MAXIMIZE:O_MINIMIZE),
                m_term(t),
                m_terms(t.get_manager()),
                m_offset(0),
                m_neg(false),
                m_id(),
                m_index(idx)
            {}

            objective(ast_manager& m, symbol id):
                m_type(O_MAXSMT),
                m_term(m),
                m_terms(m),
                m_offset(0),
                m_neg(false),
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
        model_converter_ref m_model_converter;
        obj_map<func_decl, unsigned> m_objective_fns;
        obj_map<func_decl, expr*> m_objective_orig;
        func_decl_ref_vector m_objective_refs;
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

        std::string to_string() const;

    private:
        void validate_feasibility(maxsmt& ms);

        lbool execute(objective const& obj, bool committed);
        lbool execute_min_max(unsigned index, bool committed);
        lbool execute_maxsat(symbol const& s, bool committed);
        lbool execute_lex();
        lbool execute_box();
        lbool execute_pareto();
        expr_ref to_expr(inf_eps const& n);

        void normalize();
        void internalize();
        bool is_maximize(expr* fml, app_ref& term, expr*& orig_term, unsigned& index);
        bool is_minimize(expr* fml, app_ref& term, expr*& orig_term, unsigned& index);
        bool is_maxsat(expr* fml, expr_ref_vector& terms, 
                       vector<rational>& weights, rational& offset, bool& neg, 
                       symbol& id, unsigned& index);
        expr* mk_maximize(unsigned index, app* t);
        expr* mk_minimize(unsigned index, app* t);
        expr* mk_maxsat(unsigned index, unsigned num_fmls, expr* const* fmls);
        expr* mk_objective_fn(unsigned index, objective_t ty, unsigned sz, expr*const* args);
        void to_fmls(expr_ref_vector& fmls);
        void from_fmls(expr_ref_vector const& fmls);
        void simplify_fmls(expr_ref_vector& fmls);

        void update_lower();

        inf_eps get_lower_as_num(unsigned idx);
        inf_eps get_upper_as_num(unsigned idx);


        opt_solver& get_solver();

        void display_objective(std::ostream& out, objective const& obj) const;
        void display_bounds(std::ostream& out, bounds_t const& b) const;


        void validate_lex();

    };

}

#endif
