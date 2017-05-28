/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_context.h

Abstract:
    Facility for running optimization problem.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/
#ifndef OPT_CONTEXT_H_
#define OPT_CONTEXT_H_

#include "ast.h"
#include "opt_solver.h"
#include "opt_pareto.h"
#include "optsmt.h"
#include "maxsmt.h"
#include "model_converter.h"
#include "tactic.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "cmd_context.h"
#include "qsat.h"

namespace opt {

    class opt_solver;

    /**
       \brief base class required by MaxSMT solvers.
       By implementing a base class, you can invoke the MaxSMT solvers
       independent of the overall optimization infrastructure.
       The caller has to supply a solver object that encapsulates 
       an incremental SAT or SMT solver. The MaxSMT solvers may assume that
       the solver object should be in a satisfiable state and contain an initial model.
    */

    class maxsat_context {
    public:        
        virtual filter_model_converter& fm() = 0;   // converter that removes fresh names introduced by simplification.
        virtual bool sat_enabled() const = 0;       // is using th SAT solver core enabled?
        virtual solver& get_solver() = 0;           // retrieve solver object (SAT or SMT solver)
        virtual ast_manager& get_manager() const = 0;      
        virtual params_ref& params() = 0;
        virtual void enable_sls(bool force) = 0;              // stochastic local search 
        virtual symbol const& maxsat_engine() const = 0; // retrieve maxsat engine configuration parameter.
        virtual void get_base_model(model_ref& _m) = 0;  // retrieve model from initial satisfiability call.
        virtual smt::context& smt_context() = 0;    // access SMT context for SMT based MaxSMT solver (wmax requires SMT core)
        virtual unsigned num_objectives() = 0;
        virtual bool verify_model(unsigned id, model* mdl, rational const& v) = 0;
        virtual void set_model(model_ref& _m) = 0;
    };

    /**
       \brief main context object for optimization.
       Hard and soft assertions, and objectives are registered with this context.
       It handles combinations of objectives.
    */

    class context : 
        public opt_wrapper, 
        public pareto_callback,
        public maxsat_context {
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
            adjust_value  m_adjust_value;
            symbol      m_id;            // for maxsmt
            unsigned    m_index;         // for maximize/minimize index

            objective(bool is_max, app_ref& t, unsigned idx):
                m_type(is_max?O_MAXIMIZE:O_MINIMIZE),
                m_term(t),
                m_terms(t.get_manager()),
                m_id(),
                m_index(idx)
            {
                if (!is_max) {
                    m_adjust_value.set_negate(true);
                }
            }

            objective(ast_manager& m, symbol id):
                m_type(O_MAXSMT),
                m_term(m),
                m_terms(m),
                m_id(id),
                m_index(0)
            {}
        };

        class scoped_state {
            ast_manager& m;
            arith_util   m_arith;
            bv_util      m_bv;
            unsigned_vector  m_hard_lim;
            unsigned_vector  m_objectives_lim;
            unsigned_vector  m_objectives_term_trail;
            unsigned_vector  m_objectives_term_trail_lim;
            map_id           m_indices;

        public:
            expr_ref_vector  m_hard;
            vector<objective> m_objectives;

            scoped_state(ast_manager& m):
                m(m),
                m_arith(m),
                m_bv(m),
                m_hard(m)
            {}
            void push();
            void pop();
            void add(expr* hard);
            bool set(ptr_vector<expr> & hard);
            unsigned add(expr* soft, rational const& weight, symbol const& id);
            unsigned add(app* obj, bool is_max);
            unsigned get_index(symbol const& id) { return m_indices[id]; }
        };

        ast_manager&        m;
        arith_util          m_arith;
        bv_util             m_bv;
        expr_ref_vector     m_hard_constraints;
        ref<opt_solver>     m_opt_solver;
        ref<solver>         m_solver;
        ref<solver>         m_sat_solver;
        scoped_ptr<pareto_base>          m_pareto;
        scoped_ptr<qe::qmax> m_qmax;
        sref_vector<model>  m_box_models;
        unsigned            m_box_index;
        params_ref          m_params;
        optsmt              m_optsmt; 
        map_t               m_maxsmts;
        scoped_state        m_scoped_state;
        vector<objective>   m_objectives;
        model_ref           m_model;
        model_converter_ref          m_model_converter;
        filter_model_converter       m_fm;
        obj_map<func_decl, unsigned> m_objective_fns;
        obj_map<func_decl, expr*>    m_objective_orig;
        func_decl_ref_vector         m_objective_refs;
        tactic_ref                   m_simplify;
        bool                         m_enable_sat;
        bool                         m_enable_sls;
        bool                         m_is_clausal;
        bool                         m_pp_neat;
        symbol                       m_maxsat_engine;
        symbol                       m_logic;
        svector<symbol>              m_labels;
        std::string                  m_unknown;
    public:
        context(ast_manager& m);
        virtual ~context();
        unsigned add_soft_constraint(expr* f, rational const& w, symbol const& id);
        unsigned add_objective(app* t, bool is_max);
        void add_hard_constraint(expr* f);
        
        void get_hard_constraints(expr_ref_vector& hard);
        expr_ref get_objective(unsigned i);

        virtual void push();
        virtual void pop(unsigned n);
        virtual bool empty() { return m_scoped_state.m_objectives.empty(); }
        virtual void set_hard_constraints(ptr_vector<expr> & hard);
        virtual lbool optimize();
        virtual void set_model(model_ref& _m) { m_model = _m; }
        virtual void get_model(model_ref& _m);
        virtual void get_box_model(model_ref& _m, unsigned index);
        virtual void fix_model(model_ref& _m);
        virtual void collect_statistics(statistics& stats) const;
        virtual proof* get_proof() { return 0; }
        virtual void get_labels(svector<symbol> & r);
        virtual void get_unsat_core(ptr_vector<expr> & r);
        virtual std::string reason_unknown() const;
        virtual void set_reason_unknown(char const* msg) { m_unknown = msg; }

        virtual void display_assignment(std::ostream& out);
        virtual bool is_pareto() { return m_pareto.get() != 0; }
        virtual void set_logic(symbol const& s) { m_logic = s; }
        void set_clausal(bool f) { m_is_clausal = f; }

        void display(std::ostream& out);
        static void collect_param_descrs(param_descrs & r);
        virtual void updt_params(params_ref const& p);
        params_ref& get_params() { return m_params; }

        expr_ref get_lower(unsigned idx);
        expr_ref get_upper(unsigned idx);

        void get_lower(unsigned idx, expr_ref_vector& es) { to_exprs(get_lower_as_num(idx), es); }
        void get_upper(unsigned idx, expr_ref_vector& es) { to_exprs(get_upper_as_num(idx), es); }

        std::string to_string() const;


        virtual unsigned num_objectives() { return m_scoped_state.m_objectives.size(); }       
        virtual expr_ref mk_gt(unsigned i, model_ref& model);
        virtual expr_ref mk_ge(unsigned i, model_ref& model);
        virtual expr_ref mk_le(unsigned i, model_ref& model);

        virtual smt::context& smt_context() { return m_opt_solver->get_context(); }
        virtual filter_model_converter& fm() { return m_fm; }
        virtual bool sat_enabled() const { return 0 != m_sat_solver.get(); }
        virtual solver& get_solver();
        virtual ast_manager& get_manager() const { return this->m; }
        virtual params_ref& params() { return m_params; }
        virtual void enable_sls(bool force);
        virtual symbol const& maxsat_engine() const { return m_maxsat_engine; }
        virtual void get_base_model(model_ref& _m);


        virtual bool verify_model(unsigned id, model* mdl, rational const& v);

    private:
        lbool execute(objective const& obj, bool committed, bool scoped);
        lbool execute_min_max(unsigned index, bool committed, bool scoped, bool is_max);
        lbool execute_maxsat(symbol const& s, bool committed, bool scoped);
        lbool execute_lex();
        lbool execute_box();
        lbool execute_pareto();
        lbool adjust_unknown(lbool r);
        bool scoped_lex();
        expr_ref to_expr(inf_eps const& n);
        void to_exprs(inf_eps const& n, expr_ref_vector& es);

        void reset_maxsmts();
        void import_scoped_state();
        void normalize();
        void internalize();
        bool is_maximize(expr* fml, app_ref& term, expr_ref& orig_term, unsigned& index);
        bool is_minimize(expr* fml, app_ref& term, expr_ref& orig_term, unsigned& index);
        bool is_maxsat(expr* fml, expr_ref_vector& terms, 
                       vector<rational>& weights, rational& offset, bool& neg, 
                       symbol& id, expr_ref& orig_term, unsigned& index);
        void  purify(app_ref& term);
        app* purify(filter_model_converter_ref& fm, expr* e);
        bool is_mul_const(expr* e);
        expr* mk_maximize(unsigned index, app* t);
        expr* mk_minimize(unsigned index, app* t);
        expr* mk_maxsat(unsigned index, unsigned num_fmls, expr* const* fmls);
        expr* mk_objective_fn(unsigned index, objective_t ty, unsigned sz, expr*const* args);
        void to_fmls(expr_ref_vector& fmls);
        void from_fmls(expr_ref_vector const& fmls);
        void simplify_fmls(expr_ref_vector& fmls);
        void mk_atomic(expr_ref_vector& terms);

        void update_lower() { update_bound(true); }
        void update_bound(bool is_lower);

        inf_eps get_lower_as_num(unsigned idx);
        inf_eps get_upper_as_num(unsigned idx);


        struct is_bv;
        bool probe_bv();

        struct is_propositional_fn;
        bool is_propositional(expr* e);

        void    init_solver();
        void    update_solver();
        void    setup_arith_solver();
        void    add_maxsmt(symbol const& id, unsigned index);
        void    set_simplify(tactic *simplify);
        void    set_pareto(pareto_base* p);        
        void    clear_state();

        bool is_numeral(expr* e, rational& n) const;

        void display_objective(std::ostream& out, objective const& obj) const;
        void display_bounds(std::ostream& out, bounds_t const& b) const;

        std::string to_string(expr_ref_vector const& hard, vector<objective> const& objectives) const;
        std::string to_string_internal() const;


        void validate_lex();
        void validate_maxsat(symbol const& id);

        void display_benchmark();

        // pareto
        void yield();
        expr_ref mk_ge(expr* t, expr* s);
        expr_ref mk_cmp(bool is_ge, model_ref& mdl, objective const& obj);


        // quantifiers
        bool is_qsat_opt();
        lbool run_qsat_opt();
    };

}

#endif
