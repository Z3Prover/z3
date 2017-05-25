/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"

namespace lean {
    class lar_solver;
}


namespace nra {



    class solver {
        struct imp;
        imp* m_imp;

    public:

        solver(lean::lar_solver& s, reslimit& lim, params_ref const& p = params_ref());
        
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
        lbool check(lean::explanation_t& ex);

        /*
          \brief determine whether nra check is needed.
        */
        bool need_check();

        /*
          \brief Access model.
        */
        nlsat::anum const& value(lean::var_index v) const;

        /*
          \brief push and pop scope. 
          Monomial definitions are retraced when popping scope.
        */
        void push();
        
        void pop(unsigned n);

        /*
          \brief display state
         */
        std::ostream& display(std::ostream& out) const;

    };
}
