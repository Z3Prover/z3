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

#include "solver.h"
#include "opt_solver.h"

namespace opt {

    class maxsmt_solver {
    public:        
        virtual ~maxsmt_solver() {}
        virtual lbool operator()() = 0;
        virtual rational get_lower() const = 0;
        virtual rational get_upper() const = 0;
        virtual rational get_value() const = 0;
        virtual expr_ref_vector get_assignment() const = 0;
        virtual void set_cancel(bool f) = 0;
    };
    /**
       Takes solver with hard constraints added.
       Returns modified soft constraints that are maximal assignments.
    */

    class maxsmt {
        ast_manager&     m;
        solver*          m_s;
        volatile bool    m_cancel;
        expr_ref_vector  m_soft_constraints;
        expr_ref_vector  m_answer;
        vector<rational> m_weights;
        scoped_ptr<maxsmt_solver> m_msolver;
        symbol           m_maxsat_engine;
    public:
        maxsmt(ast_manager& m): m(m), m_s(0), m_cancel(false), m_soft_constraints(m), m_answer(m) {}

        lbool operator()(solver& s);

        void set_cancel(bool f);

        void updt_params(params_ref& p);

        void add(expr* f, rational const& w) {
            m_soft_constraints.push_back(f);
            m_weights.push_back(w);
        }

        void commit_assignment();
        inf_eps get_value() const;
        inf_eps get_lower() const;
        inf_eps get_upper() const;

        expr_ref_vector get_assignment() const;

        void display_answer(std::ostream& out) const;

    private:

        bool is_maxsat_problem(vector<rational> const& ws) const;        

    };

};

#endif
