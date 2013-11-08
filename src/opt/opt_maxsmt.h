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
        ast_manager&  m;
        opt_solver*   s;
        volatile bool m_cancel;
        symbol        m_engine;
    public:
        maxsmt(ast_manager& m): m(m), s(0), m_cancel(false) {}

        lbool operator()(opt_solver& s, expr_ref_vector& soft, vector<rational> const& weights);

        void set_cancel(bool f);

        void set_engine(symbol const& e) { m_engine = e; }

    private:

        bool is_maxsat_problem(vector<rational> const& ws) const;        

    };

};

#endif
