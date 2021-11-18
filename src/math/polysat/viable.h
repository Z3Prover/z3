/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains


Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

    NEW_VIABLE uses cheaper book-keeping, but is partial.
  

--*/
#pragma once

#include <limits>
#include "math/dd/dd_bdd.h"
#include "math/polysat/types.h"


namespace polysat {

    class solver;


    class viable {
        typedef dd::bdd bdd;
        typedef dd::fdd fdd;
        solver&                      s;
        dd::bdd_manager              m_bdd;
        scoped_ptr_vector<dd::fdd>   m_bits;        
        vector<bdd>                  m_viable;   // set of viable values.
        vector<std::pair<pvar, bdd>> m_viable_trail;


        /**
         * Register all values that are not contained in vals as non-viable.
         */
        void intersect_viable(pvar v, bdd vals);

        dd::bdd_manager& get_bdd() { return m_bdd; }
        dd::fdd const& sz2bits(unsigned sz);
        dd::fdd const& var2bits(pvar v);


        void push_viable(pvar v);

    public:
        viable(solver& s);

        ~viable();

        void push(unsigned num_bits) { 
            m_viable.push_back(m_bdd.mk_true()); 
        }

        void pop() {
            m_viable.pop_back();
        }

        void pop_viable();

        void push_viable() {}
        /**
         * update state of viable for pvar v
         * based on affine constraints
         */

        void intersect_eq(rational const& a, pvar v, rational const& b, bool is_positive);

        void intersect_ule(pvar v, rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive);

        /**
         * Check whether variable v has any viable values left according to m_viable.
         */
        bool has_viable(pvar v);

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(pvar v, rational const& val);

        /*
        * Extract min and max viable values for v
        */
        rational min_viable(pvar v);

        rational max_viable(pvar v);

        /**
         * Find a next viable value for variable.
         */
        dd::find_t find_viable(pvar v, rational & val);

        /** Log all viable values for the given variable.
         * (Inefficient, but useful for debugging small instances.)
         */
        void log(pvar v);

        /** Like log(v) but for all variables */
        void log();

    };
}


