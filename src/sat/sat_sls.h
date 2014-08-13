/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_sls.h

Abstract:
   
    SLS for clauses in SAT solver

Author:

    Nikolaj Bjorner (nbjorner) 2014-12-8

Notes:

--*/
#ifndef _SAT_SLS_H_
#define _SAT_SLS_H_

#include "util.h"
#include "sat_simplifier.h"

namespace sat {

    class index_set {
        unsigned_vector m_elems;
        unsigned_vector m_index;        
    public:
        unsigned num_elems() const { return m_elems.size(); }        
        void reset() { m_elems.reset(); m_index.reset(); }        
        bool empty() const { return m_elems.empty(); }        
        bool contains(unsigned idx) const;        
        void insert(unsigned idx);        
        void remove(unsigned idx);        
        unsigned choose(random_gen& rnd) const;
    };

    class sls {
        solver&    s;
        random_gen m_rand;
        unsigned   m_max_tries;
        unsigned   m_prob_choose_min_var;      // number between 0 and 99.
        ptr_vector<clause const>    m_clauses; // vector of all clauses.
        index_set        m_false;              // clauses currently false
        vector<unsigned_vector>  m_use_list;   // use lists for literals
        unsigned_vector  m_num_true;           // per clause, count of # true literals
        svector<literal> m_min_vars;           // literals with smallest break count
        model            m_model;              // current model
        clause_allocator m_alloc;              // clause allocator
        clause_vector    m_bin_clauses;        // binary clauses
        svector<bool>    m_tabu;               // variables that cannot be swapped
    public:
        sls(solver& s);
        ~sls();        
        lbool operator()(unsigned sz, literal const* tabu);
    private:
        bool local_search();
        void init(unsigned sz, literal const* tabu);
        void init_model(unsigned sz, literal const* tabu);
        void init_use();
        void init_clauses();
        bool pick_flip(literal& lit);
        void flip();
        unsigned get_break_count(literal lit, unsigned min_break);
        unsigned_vector const& get_use(literal lit);        
    };

};

#endif
