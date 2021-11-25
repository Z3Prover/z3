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
#include "math/polysat/conflict.h"
#include "math/polysat/constraint.h"

namespace polysat {

    class solver;

    class viable {
        solver& s;
        
        struct entry : public dll_base<entry>, public fi_record { 
        public: 
            entry() : fi_record({ eval_interval::full(), {}, {} }) {}
        };
        
        ptr_vector<entry>                    m_alloc;
        ptr_vector<entry>                    m_viable;   // set of viable values.
        svector<std::pair<pvar, entry*>>     m_trail;    // undo stack

        bool well_formed(entry* e);

        entry* alloc_entry();

        bool intersect(pvar v, entry* e);

    public:
        viable(solver& s);

        ~viable();

        // declare and remove var
        void push(unsigned) { m_viable.push_back(nullptr); }

        void pop() { m_viable.pop_back(); }

        void pop_viable();

        void push_viable();

        /**
         * update state of viable for pvar v
         * based on affine constraints
         */
        bool intersect(pvar v, signed_constraint const& c);

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

        /**
        * Retrieve the unsat core for v.
        * \pre there are no viable values for v
        */
        bool resolve(pvar v, conflict& core);

        /** Log all viable values for the given variable.
         * (Inefficient, but useful for debugging small instances.)
         */
        void log(pvar v);

        /** Like log(v) but for all variables */
        void log();

        std::ostream& display(std::ostream& out) const;

        class iterator {
            entry* curr = nullptr;
            bool   visited = false;
        public:
            iterator(entry* curr, bool visited) : 
                curr(curr), visited(visited || !curr) {}

            iterator& operator++() {
                visited = true;
                curr = curr->next();
                return *this;
            }

            signed_constraint& operator*() { 
                return curr->src; 
            }

            bool operator==(iterator const& other) const {
                return visited == other.visited && curr == other.curr;
            }

            bool operator!=(iterator const& other) const {
                return !(*this == other);
            }
        };

        class constraints {
            viable& v;
            pvar var;
        public:
            constraints(viable& v, pvar var) : v(v), var(var) {}
            iterator begin() const { return iterator(v.m_viable[var], false); }
            iterator end() const { return iterator(v.m_viable[var], true); }
        };

        constraints get_constraints(pvar v) { 
            return constraints(*this, v); 
        }

        std::ostream& display(std::ostream& out, pvar v) const;

        struct var_pp {
            viable& v;
            pvar var;        
            var_pp(viable& v, pvar var) : v(v), var(var) {}
        };
       
    };

    inline std::ostream& operator<<(std::ostream& out, viable const& v) {
        return v.display(out);
    }

    inline std::ostream& operator<<(std::ostream& out, viable::var_pp const& v) {
        return v.v.display(out, v.var);
    }
}


