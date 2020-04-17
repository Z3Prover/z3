/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    sat_bcd.h

Abstract:

    Blocked Clause Decomposition.
    Exposes a partition of literals based on randomly simulating the BCD.

Author:

    Nikolaj Bjorner (nbjorner) 2014-09-27.

Revision History:

----*/
#pragma once

#include"sat/sat_types.h"
#include"sat/sat_simplifier.h"
#include"util/union_find.h"

namespace sat {

    class solver;

    class bcd {
        struct report;
        struct scoped_cleanup;

        typedef std::pair<literal, literal> bin_clause;
        typedef svector<bin_clause> bin_clauses;        
        struct bclause {
            clause* cls;
            literal lit;
            bclause(literal lit, clause* cls):cls(cls), lit(lit) {}
        };
        solver &          s;
        clause_vector     m_clauses;
        svector<bclause>  m_L, m_R, m_live_clauses, m_new_L;
        clause_vector     m_bin_clauses;
        svector<uint64_t> m_rbits;
        bool_vector     m_marked;
        bool_vector     m_removed; // set of clauses removed (not considered in clause set during BCE)

        void init(use_list& ul);
        void register_clause(clause* cls);
        void unregister_clause(clause const& cls);
        void reset_removed() { m_removed.reset(); }
        void set_removed(clause const& c) { m_removed.setx(c.id(), true, false); }
        bool is_removed(clause const& c) const { return m_removed.get(c.id(), false); }
        void pure_decompose();
        void pure_decompose(use_list& ul, literal lit);
        void pure_decompose(use_list& ul, literal lit, svector<bclause>& clauses);
        void post_decompose();
        literal find_blocked(use_list& ul, clause const& cls);
        bool bce(use_list& ul, clause& cls);
        bool is_blocked(use_list& ul, literal lit) const;
        void init_rbits();
        void init_reconstruction_stack();
        void sat_sweep();
        void cleanup();
        uint64_t eval_clause(clause const& cls) const;
        void verify_sweep();
        void extract_partition(union_find<>&);
    public:
        bcd(solver & s);
        ~bcd();
        void operator()(clause_vector& clauses, svector<bin_clause>& bins);
        void operator()(union_find<>& uf);
    };

};

