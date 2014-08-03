/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mus.h

Abstract:
   
    Basic MUS extraction

Author:

    Nikolaj Bjorner (nbjorner) 2014-20-7

Notes:

--*/
#ifndef _MUS_H_
#define _MUS_H_

namespace opt {
    class mus {
        struct imp;
        imp * m_imp;
    public:
        mus(ref<solver>& s, ast_manager& m);
        ~mus();
        /**
           Add soft constraint.

           Assume that the solver context enforces that 
           cls is equivalent to a disjunction of args.
           Assume also that cls is a literal.           
        */
        unsigned add_soft(expr* cls);
        
        lbool get_mus(unsigned_vector& mus);
        
        void reset();
        
        void set_cancel(bool f);
    };

};

#endif
