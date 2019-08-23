/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_drat.h

Abstract:
   
    Produce DRAT proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2017-2-3

Notes:

--*/
#ifndef SAT_DRAT_H_
#define SAT_DRAT_H_

namespace sat {
    class drat {
    public:
        struct s_ext {};
        struct s_unit {};
        struct premise {
            enum { t_clause, t_unit, t_ext } m_type;
            union {
                clause* m_clause;
                unsigned m_literal;                
            };
            premise(s_ext, literal l): m_type(t_ext), m_literal(l.index()) {}
            premise(s_unit, literal l): m_type(t_unit), m_literal(l.index()) {}
            premise(clause* c): m_type(t_clause), m_clause(c) {}
        };
    private:
        enum status { asserted, learned, deleted, external };
        struct watched_clause {
            clause* m_clause;
            literal m_l1, m_l2;
            watched_clause(clause* c, literal l1, literal l2):
                m_clause(c), m_l1(l1), m_l2(l2) {}
        };
        svector<watched_clause>   m_watched_clauses;
        typedef svector<unsigned> watch;
        solver& s;
        clause_allocator        m_alloc;
        std::ostream*           m_out;
        std::ostream*           m_bout;
        ptr_vector<clause>      m_proof;
        svector<status>         m_status;        
        literal_vector          m_units;
        vector<watch>           m_watches;
        svector<lbool>          m_assignment;
        bool                    m_inconsistent;
        unsigned                m_num_add, m_num_del;
        bool                    m_check_unsat, m_check_sat, m_check, m_activity;

        void dump_activity();
        void dump(unsigned n, literal const* c, status st);
        void bdump(unsigned n, literal const* c, status st);
        void append(literal l, status st);
        void append(literal l1, literal l2, status st);
        void append(clause& c, status st);

        bool is_clause(clause& c, literal l1, literal l2, literal l3, status st1, status st2);

        friend std::ostream& operator<<(std::ostream & out, status st);
        status get_status(bool learned) const;

        void declare(literal l);
        void assign(literal l);
        void propagate(literal l);
        void assign_propagate(literal l);
        void del_watch(clause& c, literal l);
        bool is_drup(unsigned n, literal const* c);
        bool is_drat(unsigned n, literal const* c);
        bool is_drat(unsigned n, literal const* c, unsigned pos);
        lbool value(literal l) const; 
        void trace(std::ostream& out, unsigned n, literal const* c, status st);
        void display(std::ostream& out) const;
        void validate_propagation() const;
        bool match(unsigned n, literal const* lits, clause const& c) const;

    public:
        drat(solver& s);
        ~drat();  

        void updt_config();
        void add();
        void add(literal l, bool learned);
        void add(literal l1, literal l2, bool learned);
        void add(clause& c, bool learned);
        void add(literal_vector const& c, svector<premise> const& premises);
        void add(literal_vector const& c); // add learned clause

        bool is_cleaned(clause& c) const;        
        void del(literal l);
        void del(literal l1, literal l2);
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
    };

};

#endif
