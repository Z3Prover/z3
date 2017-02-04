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
        enum status { asserted, learned, deleted };

        solver& s;
        std::ostream*           m_out;
        ptr_vector<clause>      m_proof;
        svector<status>         m_status;
        literal_vector          m_units;
        vector<watch_list>      m_watches;
        char_vector             m_assignment;

        void dump(unsigned n, literal const* lits, status st);
        void append(unsigned n, literal const* lits, status st);
        friend std::ostream& operator<<(std::ostream & out, status st);
        status get_status(bool learned) const;
        bool is_cleaned(unsigned n, literal const* lits) const;

    public:
        drat(solver& s);
        ~drat();  
        void add();
        void add(literal l, bool learned);
        void add(literal l1, literal l2, bool learned);
        void add(literal l1, literal l2, literal l3, bool learned);
        void add(clause& c, bool learned);
        void del(literal l);
        void del(literal l1, literal l2);
        void del(clause& c);
    };

};

#endif
