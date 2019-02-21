/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_big.h

Abstract:

    binary implication graph structure.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-13.

Revision History:

--*/
#ifndef SAT_BIG_H_
#define SAT_BIG_H_

#include "sat/sat_types.h"
#include "util/statistics.h"
#include "util/params.h"

namespace sat {
    class solver;

    class big {
        random_gen&            m_rand;
        unsigned               m_num_vars;
        vector<literal_vector> m_dag;
        svector<bool>          m_roots;
        svector<int>           m_left, m_right;
        literal_vector         m_root, m_parent;
        bool                   m_learned;
        bool                   m_include_cardinality;

        vector<svector<literal> > m_del_bin;
        

        void init_dfs_num();
        struct pframe;

        bool safe_reach(literal u, literal v);
        literal next(literal u, literal v) const;

        std::ostream& display_path(std::ostream& out, literal u, literal v) const;

        void add_del(literal u, literal v);
        bool in_del(literal u, literal v) const;

    public:

        // static svector<std::pair<literal, literal>> s_del_bin;

        big(random_gen& rand);

        void set_include_cardinality(bool f) { m_include_cardinality = f; }
        
        /**
           \brief initialize a BIG from a solver.
         */
        void init(solver& s, bool learned);

        void reinit();

        /**
           \brief initialize a BIG externally by adding implications.
        */
        void init_adding_edges(unsigned num_vars, bool learned);
        void add_edge(literal u, literal v);
        void done_adding_edges();

        void ensure_big(solver& s, bool learned) { if (m_left.empty()) init(s, learned); }

        unsigned reduce_tr(solver& s);

        // does it include learned binaries?
        bool learned() const { return m_learned; }
        int get_left(literal l) const { return m_left[l.index()]; }
        int get_right(literal l) const { return m_right[l.index()]; }
        literal get_parent(literal l) const { return m_parent[l.index()]; }
        literal get_root(literal l);
        bool reaches(literal u, literal v) const { return m_left[u.index()] < m_left[v.index()] && m_right[v.index()] < m_right[u.index()]; }        
        bool connected(literal u, literal v) const { return reaches(u, v) || reaches(~v, ~u); }
        void display(std::ostream& out) const;

    };
};

#endif
