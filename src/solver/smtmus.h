/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    smtmus.h

Abstract:
   
    MUS extraction with model rotation.

Author:

    Jaroslav Bendik, Nikolaj Bjorner (nbjorner) 2021-12-20

Notes:

--*/
#pragma once

class smtmus {
    struct imp;
    imp * m_imp;
 public:
    smtmus(solver& s);
    ~smtmus();
    
    /**
       Add soft constraint.       
    */
    unsigned add_soft(expr* cls);

    void add_soft(unsigned sz, expr* const* clss) {
        for (unsigned i = 0; i < sz; ++i)
            add_soft(clss[i]);
    }    

    /**
       Retrieve mus over soft constraints
    */
    lbool get_mus(expr_ref_vector& mus);
    
        
};


