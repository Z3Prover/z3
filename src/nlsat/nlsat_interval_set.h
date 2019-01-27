/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_interval_set.h

Abstract:

    Sets of disjoint infeasible intervals.

Author:

    Leonardo de Moura (leonardo) 2012-01-11.

Revision History:

--*/
#ifndef NLSAT_INTERVAL_SET_H_
#define NLSAT_INTERVAL_SET_H_

#include "nlsat/nlsat_types.h"

namespace nlsat {

    class interval_set;

    class interval_set_manager {
        anum_manager &           m_am;
        small_object_allocator & m_allocator;
        svector<char>            m_already_visited;
        random_gen               m_rand;
        void del(interval_set * s);
    public:
        interval_set_manager(anum_manager & m, small_object_allocator & a);
        ~interval_set_manager();
        
        void set_seed(unsigned s) { m_rand.set_seed(s); }

        /**
           \brief Return the empty set.
        */
        interval_set * mk_empty() { return nullptr; }
        
        /**
           \brief Return a set of composed of a single interval.
        */
        interval_set * mk(bool lower_open, bool lower_inf, anum const & lower, 
                          bool upper_open, bool upper_inf, anum const & upper,
                          literal justification);
        
        /**
           \brief Return the union of two sets.
        */
        interval_set * mk_union(interval_set const * s1, interval_set const * s2);
        
        /**
           \brief Reference counting
        */
        void dec_ref(interval_set * s);
        void inc_ref(interval_set * s);
        
        /**
           \brief Return true if s is the empty set.
        */
        bool is_empty(interval_set const * s) {
            return s == nullptr;
        }
        
        /**
           \brief Return true if the set contains all real numbers.
        */
        bool is_full(interval_set const * s);

        /**
           `\brief Return true if s1 is a subset of s2.
        */
        bool subset(interval_set const * s1, interval_set const * s2);

        /**
           \brief Return true if s1 and s2 cover the same subset of R.
           The justifications are ignored
        */
        bool set_eq(interval_set const * s1, interval_set const * s2);
        
        /**
           \brief Return true if s1 and s2 are the same (the justifications are taking into account).
        */
        bool eq(interval_set const * s1, interval_set const * s2);

        /**
           \brief Return a set of literals that justify s.
        */
        void get_justifications(interval_set const * s, literal_vector & js);
        
        void display(std::ostream & out, interval_set const * s) const;
        
        unsigned num_intervals(interval_set const * s) const;
        
        /**
           \brief (For debugging purposes) Return one of the intervals in s.
           \pre idx < num_intervals()
        */
        interval_set * get_interval(interval_set const * s, unsigned idx) const;
        
        /**
           \brief Select a witness w in the complement of s.
           
           \pre !is_full(s)
        */
        void peek_in_complement(interval_set const * s, bool is_int, anum & w, bool randomize);
    };

    typedef obj_ref<interval_set, interval_set_manager> interval_set_ref;

    inline std::ostream & operator<<(std::ostream & out, interval_set_ref const & s) {
        s.m().display(out, s);
        return out;
    }

};

#endif
