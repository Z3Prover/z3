/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    maintain viable domains
    It uses the interval extraction functions from forbidden intervals.
    An empty viable set corresponds directly to a conflict that does not rely on 
    the non-viable variable.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once


#include <limits>
#include "util/dlist.h"
#include "util/small_object_allocator.h"
#include "math/polysat/types.h"
#include "math/polysat/constraint.h"




namespace polysat {

    class solver;

    class viable2 {
        solver& s;
        
        struct entry : public dll_base<entry>, public fi_record { 
        public: 
            entry() : fi_record({ eval_interval::full(), {}, {} }) {}
        };
        
        small_object_allocator               m_alloc;
        ptr_vector<entry>                    m_viable;   // set of viable values.
        svector<std::pair<pvar, entry*>>     m_trail;    // undo stack

    public:
        viable2(solver& s);

        ~viable2();

        void push(unsigned) {
            m_viable.push_back(nullptr);
        }

        void pop() { 
            m_viable.pop_back(); 
        }

        void pop_viable();

        /**
         * update state of viable for pvar v
         * based on affine constraints
         */
        void intersect(pvar v, signed_constraint const& c);

        /**
         * Check whether variable v has any viable values left according to m_viable.
         */
        bool has_viable(pvar v);

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(pvar v, rational const& val);

        /**
         * register that val is non-viable for var.
         */
        void add_non_viable(pvar v, rational const& val);

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


