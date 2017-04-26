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
            void negate() { m_literal.neg();  }
            bool is_left() const { return 0 == (m_id & 0x1); }
            bool is_spawned(unsigned thread_id) const { return m_spawn_id == thread_id; }

            // the left branch has an even branch_id.
            // the branch is spawned if it is even and the spawn_id is the same as the thread_id, and furthermore it is exploring the left branch.
            // it may explore the right branch, but is then not in a spawned mode. 
            // we retain the spawn id so that the spawned thread can be re-spun.
            literal get_literal(unsigned thread_id) const { return ((m_id & 0x1) == 0 && thread_id == m_spawn_id) ? ~m_literal : m_literal; }
            std::ostream& pp(std::ostream& out) const;
        };

        struct solution {
            unsigned m_thread_id;
            unsigned m_branch_id;
            solution(unsigned t, unsigned s): m_thread_id(t), m_branch_id(s) {}
            solution(): m_thread_id(0), m_branch_id(0) {}
        };

        struct stats {
            unsigned m_spawn_closed;
            unsigned m_spawn_opened;
            unsigned m_cdcl_closed;
            stats() { reset(); }
            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };

       struct conquer {
           reslimit          m_limit;
           ccc&              m_ccc;
           solver            s;
           svector<decision> decisions;
           unsigned          thread_id;
           bool              m_spawned;
           conquer(ccc& super, params_ref const& p, unsigned tid): m_ccc(super), s(p, m_limit), thread_id(tid), m_spawned(false) {}

           lbool search();
           bool  cube_decision();           
           lbool bounded_search();
           bool  push_decision(decision const& d);
           void  pop_decision(decision const& d);
           void  replay_decisions();
       };

        struct cuber {
            ccc&              m_ccc;
            lookahead         lh;
            unsigned          m_branch_id;
            unsigned          m_last_closure_level;
            unsigned_vector   m_free_threads;
            svector<decision> decisions;

            cuber(ccc& c);
            lbool search();
            lbool research();
            bool get_solved();
            void update_closure_level(decision const& d, int offset);            
            unsigned spawn_conquer();
            void     free_conquer(unsigned thread_id);
        };

        solver&         m_s;    
        queue<solution> m_solved;
        vector<queue<decision> > m_decisions;
        unsigned        m_num_conquer;
        model           m_model;
        volatile bool   m_cancel;
        ::statistics    m_lh_stats;
        stats           m_ccc_stats;
 
        void  put_decision(decision const& d);
        bool  get_decision(unsigned thread_id, decision& d);

        static std::ostream& pp(std::ostream& out, svector<decision> const& v);

        void push_model(unsigned v, bool sign);
        void set_model();
        bool trail_in_model(literal_vector const& trail) const;

        void check_non_model(char const* fn, svector<decision> const& decisions);


    public:

        ccc(solver& s): m_s(s) {}

        lbool search();

        model const& get_model() const { return m_model; }
              
        void collect_statistics(::statistics& st) { 
            st.copy(m_lh_stats);
            st.update("ccc-spawn-closed", m_ccc_stats.m_spawn_closed);
            st.update("ccc-cdcl-closed", m_ccc_stats.m_cdcl_closed);
            st.update("ccc-spawn-opened", m_ccc_stats.m_spawn_opened);
        }
    };
}

#endif

