/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/lp/lp_settings.h"

namespace lean {
    class lar_solver;
}

namespace nra {

    class solver {
        struct imp;
        imp* m_imp;

    public:

        solver(lean::lar_solver& s);
        
        ~solver();

        /*
          \brief Add a definition v = vs[0]*vs[1]*...*vs[sz-1]
          The variable v is equal to the product of variables vs.
        */
        void add_monomial(lean::var_index v, unsigned sz, lean::var_index const* vs);

        /*
          \brief Check feasiblity of linear constraints augmented by polynomial definitions
          that are added.
         */
        lean::final_check_status check(lean::nra_model_t& m, lean::explanation_t& ex);

        /*
          \brief push and pop scope. 
          Monomial definitions are retraced when popping scope.
        */
        void push();
        
        void pop(unsigned n);
    };
}
