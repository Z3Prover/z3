/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_relevant.h

Abstract:

    Relevancy propagation

Author:

    Nikolaj Bjorner (nbjorner) 2021-12-27


Clauses are split into two parts:

- Roots
- Defs

The state transitions are:

- A literal lit is assigned:
  lit appears positively in a Root clause R and no other literal in R are relevant.
  ->
  lit is set relevant

  lit is justified at search level
  -> 
  lit is set relevant

- An equality n1 = n2 is assigned:
  n1 is relevant
  -> 
  n2 is marked as relevant

- A lit is set relevant:
  -> 
  all clauses C in Defs where lit appears negatively are added to Roots

- When a clause R is added to Roots:
  R contains a positive literal lit that is relevant
  ->
  skip adding R to Roots

- When a clause R is added to Roots:
  R contains a positive literal lit, no positive literal in R are relevant
  ->
  lit is set relevant 

- When a clause C is added to Defs:
  C contains a negative literal that is relevant
  -> 
  Add C to Roots

- When an expression is set relevant:
  All non-relevant children above Boolean connectives are set relevant
  If nodes are treated as Boolean connectives because they are clausified
  to (=> cond (= n then)) and (=> (not cond) (= n else))

Replay:
  - literals that are replayed in clauses that are marked relevant are 
    marked relevant again.

  - expressions corresponding to auxiliary clauses are added as auxiliary clauses.
  
  - TBD: Are root clauses added under a scope discarded?
    The SAT solver re-initializes clauses on its own, should we just use this mechanism?

Can a literal that is not in a root be set relevant?
 - yes, if we propagate over expressions

Do we need full watch lists instead of 2-watch lists?
 - probably, but unclear. The dual SAT solver only uses 2-watch lists, but uses a large clause for tracking 
   roots.



--*/
#pragma once
#include "sat/sat_solver.h"
#include "sat/smt/sat_th.h"

namespace euf {
    class solver;
}

namespace smt {

    class relevancy {
        euf::solver&         ctx;

        enum class update { relevant_expr, relevant_var, add_clause, set_root, set_qhead };
       
        bool                                 m_enabled = false;
        svector<std::pair<update, unsigned>> m_trail;
        unsigned_vector                      m_lim;
        unsigned                             m_num_scopes = 0;
        bool_vector                          m_relevant_expr_ids; // identifiers of relevant expressions
        bool_vector                          m_relevant_var_ids;  // identifiers of relevant Boolean variables
        sat::clause_allocator                m_alloc;
        sat::clause_vector                   m_clauses;           // clauses
        bool_vector                          m_roots;             // indicate if clause is a root
        vector<unsigned_vector>              m_occurs;            // where do literals occur
        unsigned                             m_qhead = 0;         // queue head for relevancy
        svector<std::pair<sat::literal, euf::enode*>> m_queue;    // propagation queue for relevancy
        ptr_vector<euf::th_solver>          m_relevant_eh;

        // callbacks during propagation
        void relevant_eh(euf::enode* n);
        void relevant_eh(sat::literal lit);

        void push_core() { m_lim.push_back(m_trail.size()); }
        void flush() { for (; m_num_scopes > 0; --m_num_scopes) push_core(); }

        unsigned_vector& occurs(sat::literal lit) { m_occurs.reserve(lit.index() + 1); return m_occurs[lit.index()]; }

        void propagate_relevant(sat::literal lit);

        void propagate_relevant(euf::enode* n);

        void set_relevant(euf::enode* n);

    public:
        relevancy(euf::solver& ctx);

        void push() { ++m_num_scopes; }
        void pop(unsigned n);

        void add_root(unsigned n, sat::literal const* lits);
        void add_def(unsigned n, sat::literal const* lits);
        void asserted(sat::literal lit);
        void propagate();
        bool can_propagate() const { return m_qhead < m_queue.size(); }

        void mark_relevant(euf::enode* n);
        void mark_relevant(sat::literal lit);
        void merge(euf::enode* n1, euf::enode* n2);

        bool is_relevant(sat::literal lit) const { return !m_enabled || m_relevant_var_ids.get(lit.var(), false); }
        bool is_relevant(euf::enode* n) const { return !m_enabled || m_relevant_expr_ids.get(n->get_expr_id(), false); }
        bool is_relevant(expr* e) const { return !m_enabled || m_relevant_expr_ids.get(e->get_id(), false); }
        
        bool enabled() const { return m_enabled; }

        void add_relevant(euf::th_solver* th) { m_relevant_eh.push_back(th); }
    };
}
