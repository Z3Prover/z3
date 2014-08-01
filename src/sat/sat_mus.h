/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mus.h

Abstract:
   
    Faster MUS extraction based on Belov et.al. HYB (Algorithm 3, 4)

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/
#ifndef _SAT_MUS_H_
#define _SAT_MUS_H_

namespace sat {
    class mus {
        literal_vector m_core;
        literal_vector m_assumptions;
        literal_vector m_mus;
        literal_vector m_toswap;        
        solver& s;
    public:
        mus(solver& s);
        ~mus();        
        lbool operator()();
    private:
        void rmr();
        bool has_single_unsat(literal& assumption_lit);
        void find_swappable(literal lit);
        void reset();
        void set_core();
        lbool eval(literal l) const;
    };

};

#endif
