/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_eq_solver

Abstract:

    Solver-agnostic equality solving routines for sequences
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-03-01

--*/

#include "ast/rewriter/seq_eq_solver.h"

namespace seq {


    bool eq_solver::solve(eq const& e, eq_ptr& r) {
        if (solve_itos1(e, r))
            return true;
        if (solve_itos2(e, r))
            return true;

        return false;
    }

    void eq_solver::add_consequence(expr_ref const& a) {
        m_clause.reset();
        m_clause.push_back(a);
        m_add_consequence(true, m_clause);
    }

    void eq_solver::add_consequence(expr_ref const& a, expr_ref const& b) {
        m_clause.reset();
        m_clause.push_back(a);
        m_clause.push_back(b);
        m_add_consequence(true, m_clause);
    }

    /**
     * from_int(s) == from_int(t)
     * --------------------------
     * s = t or (s < 0 and t < 0)
     */
        
    bool eq_solver::match_itos1(eq const& e, expr*& a, expr*& b) {
        return 
            e.ls.size() == 1 && e.rs.size() == 1 && 
            seq.str.is_itos(e.ls[0], a) && seq.str.is_itos(e.rs[0], b);
    }

    bool eq_solver::solve_itos1(eq const& e, eq_ptr& r) {
        expr* s = nullptr, *t = nullptr;
        if (!match_itos1(e, s, t))
            return false;
        r = nullptr;
        expr_ref eq = mk_eq(s, t);
        add_consequence(eq, mk_le(s, -1));
        add_consequence(eq, mk_le(t, -1));
        return true;
    }

    /**
     * from_int(s) == ""
     * -----------------
     *       s < 0
     */
    
    bool eq_solver::match_itos2(eq const& e, expr*& s) {
        if (e.ls.size() == 1 && e.rs.empty() && seq.str.is_itos(e.ls[0], s))
            return true;
        if (e.rs.size() == 1 && e.ls.empty() && seq.str.is_itos(e.rs[0], s))
            return true;
        return false;
    }

    bool eq_solver::solve_itos2(eq const& e, eq_ptr& r) {
        expr* s = nullptr;
        if (!match_itos2(e, s))
            return false;
        r = nullptr;
        add_consequence(mk_le(s, -1));
        return true;
    }

};

