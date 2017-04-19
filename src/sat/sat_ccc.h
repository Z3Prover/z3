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
            decision(unsigned id, unsigned d, literal last):
                m_id(id), m_depth(d), m_last(last) {}
            decision(): m_id(0), m_depth(0), m_last(null_literal) {}
        };

        solver&         s;    
        queue<unsigned> m_solved;
        queue<decision> m_decisions;
        model           m_model;
        volatile bool   m_cancel;

        struct config {
            config() {
            }
        };

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        lbool conquer(solver& s);
        lbool bounded_search(solver& s, unsigned_vector& ids);

        lbool cube();

    public:
        ccc(solver& s): s(s) {}

        lbool search();
              
    };
}

#endif

