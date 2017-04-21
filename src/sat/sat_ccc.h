/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_ccc.h

Abstract:
   
    A variant of Concurrent Cube and Conquer

Author:

    Nikolaj Bjorner (nbjorner) 2017-4-17

Notes:

--*/
#ifndef _SAT_CCC_H_
#define _SAT_CCC_H_

#include "queue.h"

namespace sat {


    class ccc {
        struct decision {
            unsigned m_id;
            unsigned m_depth;
            literal  m_last;
            unsigned m_parent;
            decision(unsigned id, unsigned d, literal last, unsigned parent_id):
                m_id(id), m_depth(d), m_last(last), m_parent(parent_id) {}
            decision(): m_id(0), m_depth(0), m_last(null_literal), m_parent(0) {}
            
            std::ostream& pp(std::ostream& out) const;
        };

        solver&         s;    
        queue<unsigned> m_solved;
        queue<decision> m_decisions;
        model           m_model;
        volatile bool   m_cancel;

        svector<bool>   m_values;

        struct config {
            config() {
            }
        };

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        lbool conquer(solver& s);
        lbool bounded_search(solver& s, svector<decision>& decisions);
        lbool cube();

        void replay_decisions(solver& s, svector<decision>& decisions);

        static std::ostream& pp(std::ostream& out, svector<decision> const& v);

        void push_model(unsigned v, bool sign);
        void set_model();
        bool trail_in_model(literal_vector const& trail) const;

        void check_non_model(char const* fn, svector<decision> const& decisions);

    public:

        ccc(solver& s): s(s) {}

        lbool search();

        model const& get_model() const { return m_model; }
              
    };
}

#endif

