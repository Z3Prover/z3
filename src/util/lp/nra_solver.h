/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/lp/lp_settings.h"
#include "util/lp/lar_solver.h"

namespace lean {
    class lar_solver;
}

namespace lp {

    class nra_solver {
        struct imp;
        imp* m_imp;

    public:

        nra_solver(lean::lar_solver& s);
        
        ~nra_solver();

        /*
          \brief Add a definition v = vs[0]*vs[1]*...*vs[sz-1]
          The variable v is equal to the product of variables vs.
        */
        void add_monomial(lean::var_index v, unsigned sz, lean::var_index const* vs);

        /*
          \brief Check feasiblity of linear constraints augmented by polynomial definitions
          that are added.
         */
        lean::final_check_status check_feasible();

        /*
          \brief push and pop scope. 
          Monomial definitions are retraced when popping scope.
        */
        void push();
        
        void pop(unsigned n);
    };
}
