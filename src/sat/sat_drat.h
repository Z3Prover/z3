/*++
Copyright (c) 2014 Microsoft Corporation

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
        solver& s;
        std::ostream* m_out;
    public:
        drat(solver& s);
        ~drat();  
        void add_empty();
        void add_literal(literal l);
        void add_binary(literal l1, literal l2);
        void add_ternary(literal l1, literal l2, literal l3);
        void add_clause(clause& c);
        void del_literal(literal l);
        void del_binary(literal l1, literal l2);
        void del_clause(clause& c);
    };

};

#endif
