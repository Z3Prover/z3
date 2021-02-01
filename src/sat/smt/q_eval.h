/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_eval.h

Abstract:

    Evaluation of clauses

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/
#pragma once

#include "sat/smt/q_clause.h"

namespace euf {
    class solver;
}

namespace q {

    class eval {
        euf::solver&       ctx;
        ast_manager&       m;
        expr_fast_mark1    m_mark;
        euf::enode_vector  m_eval;
        euf::enode_vector  m_indirect_nodes;
        ptr_vector<size_t> m_explain;

        struct scoped_mark_reset;

        void explain(clause& c, unsigned literal_idx, euf::enode* const* binding);
        void explain_eq(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        void explain_diseq(unsigned n, euf::enode* const* binding, expr* s, expr* t);

        // compare s, t modulo binding
        lbool compare(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        lbool compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t);
        
    public:
        eval(euf::solver& ctx);
        void explain(sat::literal l, justification& j, sat::literal_vector& r, bool probing);

        lbool operator()(euf::enode* const* binding, clause& c);        
        lbool operator()(euf::enode* const* binding, clause& c, unsigned& idx);
        euf::enode* operator()(unsigned n, euf::enode* const* binding, expr* e);

        euf::enode_vector const& get_watch() { return m_indirect_nodes; }
    };
}
