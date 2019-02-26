/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
*/

#pragma once
#include "util/vector.h"
#include "util/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"

namespace lp {
    class lar_solver;
}


namespace nra {



    class solver {
        struct imp;
        imp* m_imp;

    public:

        solver(lp::lar_solver& s, reslimit& lim, params_ref const& p = params_ref());
        
        ~solver();

        /*
          \brief Add a definition v = vs[0]*vs[1]*...*vs[sz-1]
          The variable v is equal to the product of variables vs.
        */
        void add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs);

        /*
          \brief Check feasiblity of linear constraints augmented by polynomial definitions
          that are added.
         */
        lbool check(lp::explanation_t& ex);

        /*
          \brief determine whether nra check is needed.
        */
        bool need_check();

        /*
          \brief Access model.
        */
        nlsat::anum const& value(lp::var_index v) const;

        nlsat::anum_manager& am();        

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
