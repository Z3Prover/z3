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

The goal is to establish a labeling of literals as "relevant" such that
- the set of relevant literals satisfies Roots
- there is a set of blocked literals that can be used to satisfy the clauses in Defs
  independent of their real assignment.

The idea is that the Defs clauses are obtained from Tseitin transformation so they can be
grouped by the blocked literal that was used to introduce them.
For example, when clausifying (and a b) we have the clauses
(=> (and a b) a)
(=> (and a b) b)
(or (not a) (not b) (and a b))
then the literal for "(and a b)" is blocked.
And recursively for clauses introduced for a, b if they use a Boolean connectives
at top level.

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
  all clauses D in Defs where lit appears negatively are added to Roots

- When a clause R is added to Roots:
  R contains a positive literal lit that is relevant
  ->
  skip adding R to Roots

- When a clause R is added to Roots:
  R contains a positive literal lit, no positive literal in R are relevant
  ->
  lit is set relevant 

- When a clause D is added to Defs:
  D contains a negative literal that is relevant
  -> 
  Add D to Roots

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


   State machine for literals: relevant(lit), assigned(lit)

relevant(lit) transitions false -> true
   if assigned(lit):     add to propagation queue
   if not assigned(lit): no-op (or mark enodes as relevant)

assigned(lit) transitions false -> true
   if relevant(lit):      add to propagation queue
   if not relevant(lit):  set relevant if member of root, add to propagation queue


--*/
#pragma once
#include "sat/sat_solver.h"
#include "sat/smt/sat_th.h"


namespace euf {

    class solver;

    class relevancy {
        euf::solver&         ctx;

        enum class update { relevant_var, add_queue, add_clause, set_root, set_qhead };
       
        bool                                 m_enabled = false;
        svector<std::pair<update, unsigned>> m_trail;
        unsigned_vector                      m_lim;
        unsigned                             m_num_scopes = 0;
        bool_vector                          m_relevant_var_ids;  // identifiers of relevant Boolean variables
        sat::clause_allocator                m_alloc;
        sat::clause_vector                   m_clauses;           // clauses
        bool_vector                          m_roots;             // indicate if clause is a root
        vector<unsigned_vector>              m_occurs;            // where do literals occur
        unsigned                             m_qhead = 0;         // queue head for relevancy
        svector<std::pair<sat::literal, euf::enode*>> m_queue;    // propagation queue for relevancy
        euf::enode_vector                    m_stack, m_todo;

        void push_core() { m_lim.push_back(m_trail.size()); }
        void flush() { for (; m_num_scopes > 0; --m_num_scopes) push_core(); }

        unsigned_vector& occurs(sat::literal lit) { m_occurs.reserve(lit.index() + 1); return m_occurs[lit.index()]; }

        void propagate_relevant(sat::literal lit);

        void add_to_propagation_queue(sat::literal lit);        

        void set_relevant(sat::literal lit);

        void set_asserted(sat::literal lit);

        void relevant_eh(sat::bool_var v);

        void propagate_relevant(euf::enode* n);

    public:
        relevancy(euf::solver& ctx): ctx(ctx) {}

        void push() { if (m_enabled) ++m_num_scopes; }
        void pop(unsigned n);

        void add_root(unsigned n, sat::literal const* lits);
        void add_def(unsigned n, sat::literal const* lits);
        void asserted(sat::literal lit);
        void propagate();
        bool can_propagate() const { return m_qhead < m_queue.size(); }

        void mark_relevant(euf::enode* n);
        void mark_relevant(sat::literal lit);
        void merge(euf::enode* n1, euf::enode* n2);

        bool is_relevant(sat::bool_var v) const { return !m_enabled || m_relevant_var_ids.get(v, false); }
        bool is_relevant(sat::literal lit) const { return is_relevant(lit.var()); }
        bool is_relevant(euf::enode* n) const { return !m_enabled || n->is_relevant(); }
        
        bool enabled() const { return m_enabled; }
        void set_enabled(bool e);
    };
}
