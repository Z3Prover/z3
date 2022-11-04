/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_drat.h

Abstract:
   
    Produce DRAT proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-3

Notes:

    For DIMACS input it produces DRAT proofs.

    For SMT extensions are as follows:

    Input assertion:
      i <literal>* 0

    Assertion (true modulo a theory):
      a [<theory-id>] <literal>* 0
    The if no theory id is given, the assertion is a tautology
    modulo Tseitin converison. Theory ids track whether the
    tautology is modulo a theory.
    Assertions are irredundant.

    Bridge from ast-node to boolean variable:
      b <bool-var-id> <ast-node-id> 0

    Definition of an expression (ast-node):
      e <ast-node-id> <name> <ast-node-id>* 0

    Redundant clause (theory lemma if theory id is given)
      [r [<theory-id>]] <literal>* 0

    Declaration of an auxiliary function:
      f <smtlib2-function-declaration> 0

    Garbage collection of a Boolean variable:
      g <bool-var-id> 0

    Available theories are:
      - euf   The theory lemma should be a consequence of congruence closure.
      - ba    TBD (need to also log cardinality and pb constraints)

    Life times of theory lemmas is TBD. When they are used for conflict resolution
    they are only used for the next lemma.

--*/
#pragma once

#include "sat_types.h"

namespace sat {
    class justification;
    class clause;

    struct clause_eh {
        virtual ~clause_eh() {}
        virtual void on_clause(unsigned, literal const*, status) = 0;        
    };

    class drat {
        struct stats {
            unsigned m_num_drup = 0;
            unsigned m_num_drat = 0;
            unsigned m_num_add = 0;
            unsigned m_num_del = 0;
        };
        struct watched_clause {
            clause* m_clause;
            literal m_l1, m_l2;
            watched_clause(clause* c, literal l1, literal l2):
                m_clause(c), m_l1(l1), m_l2(l2) {}
        };
        clause_eh* m_clause_eh = nullptr;
        svector<watched_clause>   m_watched_clauses;
        typedef svector<unsigned> watch;
        solver& s;
        clause_allocator        m_alloc;
        std::ostream*           m_out = nullptr;
        std::ostream*           m_bout = nullptr;
        svector<std::pair<clause&, status>> m_proof;
        svector<std::pair<literal, clause*>> m_units;
        vector<watch>           m_watches;
        svector<lbool>          m_assignment;
        vector<std::string>     m_theory;
        bool                    m_inconsistent = false;
        bool                    m_check_unsat = false;
        bool                    m_check_sat = false;
        bool                    m_check = false;
        bool                    m_activity = false;
        stats                   m_stats;


        void dump_activity();
        void dump(unsigned n, literal const* c, status st);
        void bdump(unsigned n, literal const* c, status st);
        void append(literal l, status st);
        void append(literal l1, literal l2, status st);
        void append(clause& c, status st);

        bool is_clause(clause& c, literal l1, literal l2, literal l3, status st1, status st2);

        std::ostream& pp(std::ostream & out, status st) const;
        status get_status(bool learned) const;

        void declare(literal l);
        void assign(literal l, clause* c);
        void propagate(literal l);
        void assign_propagate(literal l, clause* c);
        void del_watch(clause& c, literal l);
        bool is_drup(unsigned n, literal const* c);
        bool is_drat(unsigned n, literal const* c);
        bool is_drat(unsigned n, literal const* c, unsigned pos);
        lbool value(literal l) const; 
        void trace(std::ostream& out, unsigned n, literal const* c, status st);
        void display(std::ostream& out) const;
        void validate_propagation() const;
        bool match(unsigned n, literal const* lits, clause const& c) const;

        clause& mk_clause(clause& c);
        clause& mk_clause(unsigned n, literal const* lits, bool is_learned);


    public:

        drat(solver& s);
        ~drat();  

        void updt_config();

        void add_theory(int id, symbol const& s) { m_theory.setx(id, s.str(), std::string()); }
        void add();
        void add(literal l, bool learned);
        void add(literal l1, literal l2, status st);
        void add(clause& c, status st);
        void add(literal_vector const& c, status st);
        void add(literal_vector const& c); // add learned clause
        void add(unsigned sz, literal const* lits, status st);

        void set_clause_eh(clause_eh& clause_eh) { m_clause_eh = &clause_eh; }

        std::ostream* out() { return m_out; }

        bool is_cleaned(clause& c) const;        
        void del(literal l);
        void del(literal l1, literal l2);
        void del(literal_vector const& lits);
        void del(clause& c);

        void verify(clause const& c) { verify(c.size(), c.begin()); }
        void verify(unsigned n, literal const* c);
        void verify(literal l1, literal l2) { literal lits[2] = {l1, l2}; verify(2, lits); }
        void verify(literal l1, literal l2, literal l3) { literal lits[3] = {l1, l2, l3}; verify(3, lits); }

        bool contains(clause const& c) { return contains(c.size(), c.begin()); }
        bool contains(unsigned n, literal const* c);
        bool contains(literal l1, literal l2) { literal lits[2] = {l1, l2}; return contains(2, lits); }
        bool contains(literal l1, literal l2, literal l3) { literal lits[3] = {l1, l2, l3}; return contains(3, lits); }
        bool contains(literal c, justification const& j);

        void check_model(model const& m);

        void collect_statistics(statistics& st) const;

        bool inconsistent() const { return m_inconsistent; }
        svector<std::pair<literal, clause*>> const& units() { return m_units; }
        bool is_drup(unsigned n, literal const* c, literal_vector& units);
        solver& get_solver() { return s; }
        
    };

}


