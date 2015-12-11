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
#ifndef OPT_MAXSMT_H_
#define OPT_MAXSMT_H_

#include"ast.h"
#include"params.h"
#include"solver.h"
#include"filter_model_converter.h"
#include"statistics.h"
#include"smt_context.h"
#include"smt_theory.h"
#include"theory_wmaxsat.h"
#include"opt_solver.h"

namespace opt {

    typedef vector<rational> const weights_t;

    class maxsat_context;

    class maxsmt_solver {
    protected:
        adjust_value m_adjust_value;
    public:        
        virtual ~maxsmt_solver() {}
        virtual lbool operator()() = 0;
        virtual rational get_lower() const = 0;
        virtual rational get_upper() const = 0;
        virtual bool get_assignment(unsigned index) const = 0;
        virtual void collect_statistics(statistics& st) const = 0;
        virtual void get_model(model_ref& mdl, svector<symbol>& labels) = 0;
        virtual void updt_params(params_ref& p) = 0;
        void set_adjust_value(adjust_value& adj) { m_adjust_value = adj; }

    };

    // ---------------------------------------------
    // base class with common utilities used
    // by maxsmt solvers
    // 
    class maxsmt_solver_base : public maxsmt_solver {
    protected:
        ast_manager&     m;
        maxsat_context&  m_c;
        const expr_ref_vector  m_soft;
        vector<rational> m_weights;
        expr_ref_vector  m_assertions;
        rational         m_lower;
        rational         m_upper;
        model_ref        m_model;
        svector<symbol>  m_labels;
        svector<bool>    m_assignment;       // truth assignment to soft constraints
        params_ref       m_params;           // config

    public:
        maxsmt_solver_base(maxsat_context& c, weights_t& ws, expr_ref_vector const& soft); 

        virtual ~maxsmt_solver_base() {}        
        virtual rational get_lower() const { return m_lower; }
        virtual rational get_upper() const { return m_upper; }
        virtual bool get_assignment(unsigned index) const { return m_assignment[index]; }
        virtual void collect_statistics(statistics& st) const { }
        virtual void get_model(model_ref& mdl, svector<symbol>& labels) { mdl = m_model.get(); labels = m_labels;}
        virtual void commit_assignment();
        void set_model() { s().get_model(m_model); s().get_labels(m_labels); }
        virtual void updt_params(params_ref& p);
        solver& s();
        void init();
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
        scoped_ptr<maxsmt_solver_base> m_msolver;
        expr_ref_vector  m_soft_constraints;
        expr_ref_vector  m_answer;
        vector<rational> m_weights;
        rational         m_lower;
        rational         m_upper;
        adjust_value     m_adjust_value;
        model_ref        m_model;
        svector<symbol>  m_labels;
        params_ref       m_params;
    public:
        maxsmt(maxsat_context& c);
        lbool operator()();
        void updt_params(params_ref& p);
        void add(expr* f, rational const& w); 
        void set_adjust_value(adjust_value& adj) { m_adjust_value = adj; }
        unsigned size() const { return m_soft_constraints.size(); }
        expr* operator[](unsigned idx) const { return m_soft_constraints[idx]; }
        rational weight(unsigned idx) const { return m_weights[idx]; }
        void commit_assignment();
        rational get_value() const;
        rational get_lower() const;
        rational get_upper() const;        
        void update_lower(rational const& r);
        void update_upper(rational const& r);
        void get_model(model_ref& mdl, svector<symbol>& labels);
        bool get_assignment(unsigned index) const;
        void display_answer(std::ostream& out) const;        
        void collect_statistics(statistics& st) const;
    private:
        bool is_maxsat_problem(weights_t& ws) const;        
        void verify_assignment();
        solver& s();
    };

};

#endif
