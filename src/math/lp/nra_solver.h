/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Nikolaj Bjorner
*/

#pragma once
#include "util/vector.h"
#include "math/lp/lp_settings.h"
#include "math/polynomial/algebraic_numbers.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"
#include "math/grobner/pdd_solver.h"
#include "math/dd/dd_pdd.h"

namespace lp {
    class lar_solver;
}


namespace nra {

    class solver {
        struct imp;
        imp* m_imp;

    public:

        solver(lp::lar_solver& s, reslimit& lim, nla::core & nla_core, params_ref const& p = params_ref());
        
        ~solver();


        /*
          \brief Check feasiblity of linear constraints augmented by polynomial definitions
          that are added.
         */
        lbool check();

        /**
           \brief Check feasibility of equalities modulo bounds constraints on their variables.
         */
        lbool check(vector<dd::pdd> const& eqs);

        /**
           \brief Check feasibility with respect to a set of reduced constraints.
        */
        lbool check(dd::solver::equation_vector const& eqs);

        /*
          \brief determine whether nra check is needed.
        */
        bool need_check();

        /*
          \brief Access model.
        */
        nlsat::anum const& value(lp::lpvar v);

        nlsat::anum_manager& am();        

        scoped_anum& tmp1();

        scoped_anum& tmp2();

        void updt_params(params_ref& p);

        /*
          \brief display state
         */
        std::ostream& display(std::ostream& out) const;

    };
}
