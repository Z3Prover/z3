/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_maxsmt.h

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/
#ifndef _OPT_MAXSMT_H_
#define _OPT_MAXSMT_H_

#include "opt_solver.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns modified soft constraints that are maximal assignments.
    */

    class maxsmt {
        ast_manager&     m;
        opt_solver*      s;
        volatile bool    m_cancel;
        expr_ref_vector  m_soft_constraints;
        expr_ref_vector  m_answer;
        vector<rational> m_weights;
        symbol           m_engine;
    public:
        maxsmt(ast_manager& m): m(m), s(0), m_cancel(false), m_soft_constraints(m), m_answer(m) {}

        lbool operator()(opt_solver& s);

        void set_cancel(bool f);

        void add(expr* f, rational const& w) {
            m_soft_constraints.push_back(f);
            m_weights.push_back(w);
        }

        void set_engine(symbol const& e) { m_engine = e; }

        // TBD: rational get_value() const;

        expr_ref_vector get_assignment() const;

        void display_answer(std::ostream& out) const;

    private:

        bool is_maxsat_problem(vector<rational> const& ws) const;        

    };

};

#endif
