/*++
  Copyright (c) 2019 Microsoft Corporation

  Module Name:

   sat_ddfw.h

  Abstract:
   
    DDFW Local search module for clauses

  Author:

  Nikolaj Bjorner 2019-4-23

  Notes:
  
     http://www.ict.griffith.edu.au/~johnt/publications/CP2006raouf.pdf

  --*/
#ifndef _SAT_DDFW_
#define _SAT_DDFW_

#include "util/uint_set.h"
#include "util/heap.h"
#include "util/rlimit.h"
#include "sat/sat_clause.h"

namespace sat {
    class solver;

    class ddfw {
        struct lt {
            svector<int>& m_reward;
            lt(svector<int>& b): m_reward(b) {}
            bool operator()(bool_var v1, bool_var v2) const { return m_reward[v1] > m_reward[v2]; }
        };

        struct clause_info {
            clause_info(): m_weight(2), m_trues(0), m_num_trues(0) {}
            unsigned m_weight;       // weight of clause
            unsigned m_trues;        // set of literals that are true
            unsigned m_num_trues;    // size of true set
            bool is_true() const { return m_num_trues > 0; }
            void add(literal lit) { ++m_num_trues; m_trues += lit.index(); }
            void del(literal lit) { SASSERT(m_num_trues > 0); --m_num_trues; m_trues -= lit.index(); }
        };
        
        reslimit         m_limit;
        clause_allocator m_alloc;
        clause_vector   m_clause_db;     
        svector<clause_info> m_clauses;
        svector<int>    m_reward; // per var break count
        svector<bool>   m_values;
        heap<lt>        m_heap;
        vector<unsigned_vector> m_use_list;
        indexed_uint_set m_unsat;
        random_gen       m_rand;
        unsigned         m_plateau_counter;
        unsigned         m_plateau_inc;
        unsigned         m_plateau_lim;
        bool             m_reinit_phase;

        bool is_true(literal lit) const { return m_values[lit.var()] != lit.sign(); }

        inline clause const& get_clause(unsigned idx) const { return *m_clause_db[idx]; }

        inline unsigned get_weight(unsigned idx) const { return m_clauses[idx].m_weight; }

        inline bool is_true(unsigned idx) const { return m_clauses[idx].is_true(); }

        unsigned select_max_same_sign(clause const& c);

        void flip(bool_var v);

        void shift_weights();

        bool should_reinit_weights();
        
        void do_reinit_weights();

        void init();

        void init_rewards();

        void invariant();

    public:
        ddfw(): m_heap(10, m_reward) {}

        ~ddfw();

        lbool check();

        reslimit& rlimit() { return m_limit; }

        void add(unsigned sz, literal const* c);

        void add(solver const& s);
       
        std::ostream& display(std::ostream& out) const;
    };
}

#endif
