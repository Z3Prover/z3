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
#ifndef MUS_H_
#define MUS_H_

namespace opt {
    class mus {
        struct imp;
        imp * m_imp;
    public:
        mus(solver& s, ast_manager& m);
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
        
        /**
           Instrument MUS extraction to also provide the minimal
           penalty model, if any is found.
           The minimal penalty model has the least weight for the 
           supplied soft constraints.
         */
        void set_soft(unsigned sz, expr* const* soft, rational const* weights);
        rational get_best_model(model_ref& mdl);
        
    };

};

#endif
