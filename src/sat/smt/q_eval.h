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

#include "ast/has_free_vars.h"
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
        bool               m_freeze_swap = false;
        euf::enode_pair    m_diseq_undef;
        contains_vars      m_contains_vars;

        struct scoped_mark_reset;

        // compare s, t modulo binding
        lbool compare(unsigned n, euf::enode* const* binding, expr* s, expr* t, euf::enode_pair_vector& evidence);
        lbool compare_rec(unsigned n, euf::enode* const* binding, expr* s, expr* t, euf::enode_pair_vector& evidence);
        
    public:
        eval(euf::solver& ctx);

        lbool operator()(euf::enode* const* binding, clause& c, euf::enode_pair_vector& evidence);
        lbool operator()(euf::enode* const* binding, clause& c, unsigned& idx, euf::enode_pair_vector& evidence);
        euf::enode* operator()(unsigned n, euf::enode* const* binding, expr* e, euf::enode_pair_vector& evidence);

        euf::enode_vector const& get_watch() { return m_indirect_nodes; }
    };
}
