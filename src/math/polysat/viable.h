/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains


Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once

#include <limits>
#include "util/tbv.h"
#include "math/dd/dd_bdd.h"
#include "math/interval/mod_interval.h"
#include "math/polysat/types.h"

#define NEW_VIABLE 0

namespace polysat {

    class solver;

    //
    // replace BDDs by viable sets that emulate affine relations.
    // viable_set has an interval of feasible values.
    // it also can use ternary bit-vectors.
    //
    class viable_set : public mod_interval<rational> {
        unsigned m_num_bits;
        tbv* m_tbv = nullptr;
        void set_lo(rational const& lo);
        void set_hi(rational const& hi);
        void set_eq(rational const& val);
        void seq_ne(rational const& val);
        void set_ule(rational const& a, rational const& b, rational const& c, rational const& d);
        void set_ugt(rational const& a, rational const& b, rational const& c, rational const& d);

    public:
        viable_set(unsigned num_bits): m_num_bits(num_bits) {}
        bool is_singleton(rational& val) const; // all bits in tbv are fixed and !is_empty() for mod_interval
        void intersect_eq(rational const& a, rational const& b, bool is_positive) {}      
        void intersect_ule(rational const& a, rational const& b, rational const& c, rational const& d, bool is_positive) {}
    };

    class viable {
        typedef dd::bdd bdd;
        solver& s;
        dd::bdd_manager              m_bdd;
        scoped_ptr_vector<dd::fdd>   m_bits;
        vector<bdd>                  m_viable_bdd;   // set of viable values.
        vector<std::pair<pvar, bdd>> m_viable_trail;


        vector<viable_set>        m_viable; // future representation of viable values

        /**
         * Register all values that are not contained in vals as non-viable.
         */
        void intersect_viable(pvar v, bdd vals);

        dd::bdd_manager& get_bdd() { return m_bdd; }
        dd::fdd const& sz2bits(unsigned sz);
        dd::fdd const& var2bits(pvar v);

    public:
        viable(solver& s);

        void push(unsigned num_bits) { 
            m_viable_bdd.push_back(m_bdd.mk_true()); 
            m_viable.push_back(viable_set(num_bits)); 
        }

        void pop() { 
            m_viable_bdd.pop_back(); 
            m_viable.pop_back(); 
        }

        void push_viable(pvar v);

        void pop_viable();

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

        bool is_false(pvar v) { return !has_viable(v); }

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(pvar v, rational const& val);

        /**
         * register that val is non-viable for var.
         */
        void add_non_viable(pvar v, rational const& val);


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


