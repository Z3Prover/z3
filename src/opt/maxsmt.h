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
#ifndef _OPT_MAXSMT_H_
#define _OPT_MAXSMT_H_

#include "opt_solver.h"
#include "statistics.h"

namespace opt {

    class maxsmt_solver {
    public:        
        virtual ~maxsmt_solver() {}
        virtual lbool operator()() = 0;
        virtual rational get_lower() const = 0;
        virtual rational get_upper() const = 0;
        virtual bool get_assignment(unsigned index) const = 0;
        virtual void set_cancel(bool f) = 0;
        virtual void collect_statistics(statistics& st) const = 0;
        virtual void get_model(model_ref& mdl) = 0;
        virtual void updt_params(params_ref& p) = 0;

    };

    // ---------------------------------------------
    // base class with common utilities used
    // by maxsmt solvers
    // 
    class maxsmt_solver_base : public maxsmt_solver {
    protected:
        ref<solver>      m_s;
        ast_manager&     m;
        volatile bool    m_cancel;
        expr_ref_vector  m_soft;
        vector<rational> m_weights;
        rational         m_lower;
        rational         m_upper;
        model_ref        m_model;
        ref<filter_model_converter> m_mc;    // model converter to remove fresh variables
        svector<bool>    m_assignment;       // truth assignment to soft constraints
        params_ref       m_params;           // config
        bool             m_enable_sls;       // config
        bool             m_enable_sat;       // config
        bool             m_sls_enabled;
        bool             m_sat_enabled;
        struct is_bv;

    public:
        maxsmt_solver_base(opt_solver* s, ast_manager& m, params_ref& p,
                           vector<rational> const& ws, expr_ref_vector const& soft): 
            m_s(s), m(m), m_cancel(false), m_soft(m),
            m_enable_sls(false), m_enable_sat(false),
            m_sls_enabled(false), m_sat_enabled(false) {
            m_s->get_model(m_model);
            SASSERT(m_model);
            updt_params(p);
            set_converter(s->mc_ref().get());
            init_soft(ws, soft);
        }

        virtual ~maxsmt_solver_base() {}        
        virtual rational get_lower() const { return m_lower; }
        virtual rational get_upper() const { return m_upper; }
        virtual bool get_assignment(unsigned index) const { return m_assignment[index]; }
        virtual void set_cancel(bool f) { m_cancel = f; m_s->set_cancel(f); }
        virtual void collect_statistics(statistics& st) const { 
            if (m_sls_enabled || m_sat_enabled) {
                m_s->collect_statistics(st);
            }
        }
        virtual void get_model(model_ref& mdl) { mdl = m_model.get(); }
        void set_model() { s().get_model(m_model); }
        virtual void updt_params(params_ref& p);
        virtual void init_soft(vector<rational> const& weights, expr_ref_vector const& soft);
        void add_hard(expr* e){ s().assert_expr(e); }        
        solver& s() { return *m_s; }
        void set_converter(filter_model_converter* mc) { m_mc = mc; }
        void init();
        expr* mk_not(expr* e);
        bool probe_bv();
        void set_mus(bool f);
        void enable_bvsat();
        void enable_sls();
        app* mk_fresh_bool(char const* name);
    private:
        void enable_inc_bvsat();
    };

    /**
       Takes solver with hard constraints added.
       Returns modified soft constraints that are maximal assignments.
    */

    class maxsmt {
        ast_manager&     m;
        ref<opt_solver>  m_s;
        volatile bool    m_cancel;
        expr_ref_vector  m_soft_constraints;
        expr_ref_vector  m_answer;
        vector<rational> m_weights;
        rational         m_lower;
        rational         m_upper;
        scoped_ptr<maxsmt_solver> m_msolver;
        symbol           m_maxsat_engine;
        model_ref        m_model;
        params_ref       m_params;
    public:
        maxsmt(ast_manager& m): m(m), m_s(0), m_cancel(false), m_soft_constraints(m), m_answer(m) {}

        lbool operator()(opt_solver* s);

        void set_cancel(bool f);

        void updt_params(params_ref& p);

        void add(expr* f, rational const& w); 
        unsigned size() const { return m_soft_constraints.size(); }
        expr* operator[](unsigned idx) const { return m_soft_constraints[idx]; }
        rational weight(unsigned idx) const { return m_weights[idx]; }

        void commit_assignment();
        rational get_value() const;
        rational get_lower() const;
        rational get_upper() const;
        void update_lower(rational const& r, bool override);
        void update_upper(rational const& r, bool override);
        void get_model(model_ref& mdl);
        bool get_assignment(unsigned index) const;
        void display_answer(std::ostream& out) const;        
        void collect_statistics(statistics& st) const;

    private:

        bool is_maxsat_problem(vector<rational> const& ws) const;        

    };

};

#endif
