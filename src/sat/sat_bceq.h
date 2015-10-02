/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_bceq.h

Abstract:

    Find equivalent literals based on blocked clause decomposition.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-27.

Revision History:

--*/
#ifndef SAT_BCEQ_H_
#define SAT_BCEQ_H_

#include"sat_types.h"
#include"union_find.h"


namespace sat {
    class solver;

    class bceq {
        typedef ptr_vector<clause> clause_use_list;
        class use_list {
            vector<ptr_vector<clause> > m_clauses;
        public:
            use_list() {}
            void init(unsigned num_vars);
            void reset() { m_clauses.reset(); }
            void erase(clause& c);
            void insert(clause& c);
            ptr_vector<clause>& get(literal lit);
        };
        typedef std::pair<literal, literal> bin_clause;
        typedef svector<bin_clause> bin_clauses;        
        solver &          m_solver;
        use_list*         m_use_list;
        use_list          m_bce_use_list;
        solver*           m_s;
        random_gen        m_rand;
        svector<clause*>  m_clauses;
        svector<clause*>  m_L;
        svector<clause*>  m_R;
        literal_vector    m_L_blits;
        literal_vector    m_R_blits;
        svector<clause*>  m_bin_clauses;
        svector<uint64>   m_rbits;
        svector<clause*>  m_rstack; // stack of blocked clauses
        literal_vector    m_bstack; // stack of blocking literals
        svector<bool>     m_marked;
        svector<bool>     m_removed; // set of clauses removed (not considered in clause set during BCE)
        union_find_default_ctx m_union_find_ctx;
        unsigned_vector   m_live_clauses;

        void init();
        void register_clause(clause* cls);
        void unregister_clause(clause* cls);
        void pure_decompose();
        void pure_decompose(literal lit);
        void pure_decompose(ptr_vector<clause>& uses, svector<clause*>& clauses);
        void post_decompose();
        literal find_blocked(clause const& cls);
        bool bce(clause& cls);
        bool is_blocked(literal lit) const;
        void init_rbits();
        void init_reconstruction_stack();
        void sat_sweep();
        void cleanup();
        uint64 eval_clause(clause const& cls) const;
        void verify_sweep();
        void extract_partition();
        bool check_equality(unsigned v1, unsigned v2);
        bool is_already_equiv(literal l1, literal l2);
        void assert_equality(literal l1, literal l2);
    public:
        bceq(solver & s);
        void operator()();
    };

};

#endif
