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
            unsigned m_id;                     // unique identifier for decision 
            unsigned m_depth;                  // depth of decision
            literal  m_literal;                // decision literal 
            unsigned m_parent;                 // id of parent
            int      m_spawn_id;               // thread id of conquer thread processing complented branch.
                                               // = 0 if not spawned.
                                               // > 0 if active spawn is in progress
                                               // < 0 if thread has closed the branch
            decision(unsigned id, unsigned d, literal last, unsigned parent_id, unsigned spawn):
                m_id(id), m_depth(d), m_literal(last),  m_parent(parent_id), m_spawn_id(spawn) {}
            decision(): 
                m_id(0), m_depth(0), m_literal(null_literal), m_parent(0), m_spawn_id(0) {} 

            void close() { SASSERT(m_spawn_id > 0); m_spawn_id = -m_spawn_id; }
            bool is_closed() const { return m_spawn_id < 0; }
            void negate() { m_literal.neg(); m_spawn_id = 0; }
            literal get_literal(unsigned thread_id) const { return thread_id == m_spawn_id ? ~m_literal : m_literal; }
            std::ostream& pp(std::ostream& out) const;
        };

        struct solution {
            unsigned m_thread_id;
            unsigned m_branch_id;
            solution(unsigned t, unsigned s): m_thread_id(t), m_branch_id(s) {}
        };

        solver&         m_s;    
        queue<solution> m_solved;
        vector<queue<decision> > m_decisions;
        unsigned        m_num_conquer;
        model           m_model;
        volatile bool   m_cancel;
        unsigned        m_branch_id;
        unsigned_vector m_free_threads;
        unsigned        m_last_closure_level;
        ::statistics    m_stats;

        lbool conquer(solver& s, unsigned thread_id);
        bool  cube_decision(solver& s, svector<decision>& decisions, unsigned thread_id);

        lbool bounded_search(solver& s, svector<decision>& decisions, unsigned thread_id);
        bool  push_decision(solver& s, decision const& d, unsigned thread_id);
        lbool cube();
        lbool cube(svector<decision>& decisions, lookahead& lh);
        void  put_decision(decision const& d);
        bool  get_decision(unsigned thread_id, decision& d);
        bool  get_solved(svector<decision>& decisions);

        void replay_decisions(solver& s, svector<decision>& decisions, unsigned thread_id);

        static std::ostream& pp(std::ostream& out, svector<decision> const& v);

        void push_model(unsigned v, bool sign);
        void set_model();
        bool trail_in_model(literal_vector const& trail) const;

        void check_non_model(char const* fn, svector<decision> const& decisions);

        unsigned spawn_conquer(svector<decision> const& decisions);
        void     free_conquer(unsigned thread_id);

    public:

        ccc(solver& s): m_s(s) {}

        lbool search();

        model const& get_model() const { return m_model; }
              
        void collect_statistics(::statistics& st) { st.copy(m_stats); }
    };
}

#endif

