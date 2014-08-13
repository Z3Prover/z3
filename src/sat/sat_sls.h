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
        solver& s;
        random_gen m_rand;
        unsigned   m_max_tries;
        unsigned   m_max_flips;
        index_set  m_false;
        use_list   m_use_list;
        vector<clause> m_clauses;
    public:
        sls(solver& s);
        ~sls();        
        lbool operator()();
    private:
        bool local_search();
        bool_var pick_flip();
        void flip(bool_var v);
    };

};

#endif
