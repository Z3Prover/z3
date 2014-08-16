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
        literal_vector m_mus;
        bool           m_is_active;

        solver& s;
    public:
        mus(solver& s);
        ~mus();        
        lbool operator()();
        bool is_active() const { return m_is_active; }
    private:
        lbool mus2();
        void mr();
        void reset();
        void set_core();
    };

};

#endif
