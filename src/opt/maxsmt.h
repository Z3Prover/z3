/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsmt.h

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "solver/solver.h"
#include "util/statistics.h"
#include "smt/smt_context.h"
#include "smt/smt_theory.h"
#include "smt/theory_wmaxsat.h"
#include "opt/opt_solver.h"

namespace opt {

    typedef vector<rational> const weights_t;

    struct weighted_core {
        ptr_vector<expr>  m_core;
        rational          m_weight;
        weighted_core(ptr_vector<expr> const& c, rational const& w):
            m_core(c), m_weight(w) {}
    };

    class maxsat_context;

    class maxsmt_solver {
    public:        
        virtual ~maxsmt_solver() = default;
        virtual lbool operator()() = 0;
        virtual rational get_lower() const = 0;
        virtual rational get_upper() const = 0;
        virtual bool get_assignment(unsigned index) const = 0;
        virtual void collect_statistics(statistics& st) const = 0;
        virtual void get_model(model_ref& mdl, svector<symbol>& labels) = 0;
        virtual void updt_params(params_ref& p) = 0;

    };

    // ---------------------------------------------
    // base class with common utilities used
    // by maxsmt solvers
    //

    struct soft { 
        expr_ref  s; 
        rational  weight; 
        lbool     value;
        void set_value(bool t) { value = t?l_true:l_undef; }
        void set_value(lbool t) { value = t; }
        bool is_true() const { return value == l_true; }
        soft(expr_ref const& s, rational const& w, bool t): s(s), weight(w), value(t?l_true:l_undef) {}
    };

    class maxsmt_solver_base : public maxsmt_solver {
    protected:
        ast_manager&     m;
        maxsat_context&  m_c;
        unsigned         m_index;
        vector<soft>&    m_soft;
        expr_ref_vector  m_assertions;
        expr_ref_vector  m_trail;
        rational         m_lower;
        rational         m_upper;
        model_ref        m_model;
        svector<symbol>  m_labels;
        params_ref       m_params;           // config

    public:
        maxsmt_solver_base(maxsat_context& c, vector<soft>& soft, unsigned index);
        
        rational get_lower() const override { return m_lower; }
        rational get_upper() const override { return m_upper; }
        bool get_assignment(unsigned index) const override { return m_soft[index].is_true(); }
        void collect_statistics(statistics& st) const override { }
        void get_model(model_ref& mdl, svector<symbol>& labels) override { mdl = m_model.get(); labels = m_labels;}
        virtual void commit_assignment();
        void set_model() { s().get_model(m_model); s().get_labels(m_labels); }
        void updt_params(params_ref& p) override;
        solver& s();
        bool init();
        void set_mus(bool f);
        app* mk_fresh_bool(char const* name);

        class smt::theory_wmaxsat* get_wmax_theory() const;
        smt::theory_wmaxsat* ensure_wmax_theory();
        class scoped_ensure_theory {
            smt::theory_wmaxsat* m_wth;
        public:
            scoped_ensure_theory(maxsmt_solver_base& s);
            ~scoped_ensure_theory();
            smt::theory_wmaxsat& operator()();
        };

        void reset_upper();
        

    protected:
        void enable_sls(bool force);
        void trace_bounds(char const* solver);

    };

    /**
       Takes solver with hard constraints added.
       Returns modified soft constraints that are maximal assignments.
    */

    class maxsmt {
        ast_manager&              m;
        maxsat_context&           m_c;
        unsigned                  m_index;
        scoped_ptr<maxsmt_solver_base> m_msolver;
        vector<soft>     m_soft;
        obj_map<expr, unsigned> m_soft_constraint_index;
        expr_ref_vector  m_answer;
        rational         m_lower;
        rational         m_upper;
        model_ref        m_model;
        svector<symbol>  m_labels;
        params_ref       m_params;
    public:
        maxsmt(maxsat_context& c, unsigned id);
        lbool operator()(bool committed);
        void updt_params(params_ref& p);
        void add(expr* f, rational const& w); 
        unsigned size() const { return m_soft.size(); }
        expr* operator[](unsigned idx) const { return m_soft[idx].s; }
        rational weight(unsigned idx) const { return m_soft[idx].weight; }
        void commit_assignment();
        rational get_lower() const;
        rational get_upper() const;        
        void update_lower(rational const& r);
        void update_upper(rational const& r);
        void get_model(model_ref& mdl, svector<symbol>& labels);
        bool get_assignment(unsigned index) const;
        void display_answer(std::ostream& out) const;        
        void collect_statistics(statistics& st) const;
        void model_updated(model* mdl);
        void reset_upper();
    private:
        bool is_maxsat_problem(weights_t& ws) const;        
        void verify_assignment();
        solver& s();
    };

    /**
       \brief Standalone MaxSMT solver.

       It takes as input a solver object and provides a MaxSAT solver routine.

       It assumes the solver state is satisfiable and therefore there is a model
       associated with the constraints asserted to the solver. A model of the 
       solver state must be supplied as a last argument.

       It assumes that the caller manages scope on the solver such that
       the solver can be left in a stronger or inconsistent state upon return.
       Callers should therefore use this feature under a push/pop.
    */
    class maxsmt_wrapper {
        params_ref  m_params;
        ref<solver> m_solver;
        model_ref   m_model;
    public:
        maxsmt_wrapper(params_ref & p, solver* s, model* m): 
            m_params(p), 
            m_solver(s),
            m_model(m) {}
        
        lbool operator()(expr_ref_vector& soft) {
            vector<std::pair<expr*, rational>> _soft;
            for (expr* e : soft) _soft.push_back(std::make_pair(e, rational::one()));
            lbool r = (*this)(_soft);
            soft.reset();
            for (auto const& p : _soft) soft.push_back(p.first);
            return r;
        }

        /**
           \brief takes a vector of weighted soft constraints.
           Returns a modified list of soft constraints that are 
           satisfied in the maximal satisfying assignment.
        */
        lbool operator()(vector<std::pair<expr*,rational>> & soft);

        model_ref get_model() { return m_model; }
    };

};

