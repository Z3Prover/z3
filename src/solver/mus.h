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

class mus {
    struct imp;
    imp * m_imp;
 public:
    mus(solver& s);
    ~mus();
    /**
       Add soft constraint.
       
       Assume that the solver context enforces that 
       cls is equivalent to a disjunction of args.
       Assume also that cls is a literal.           
    */
    unsigned add_soft(expr* cls);

    void add_soft(unsigned sz, expr* const* clss) {
        for (unsigned i = 0; i < sz; ++i) add_soft(clss[i]);
    }
    
    /**
       Additional assumption for solver to be used along with solver context, 
       but not used in core computation. This facility is useful when querying
       for a core over only a subset of soft constraints. It has the same 
       logical functionality as asserting 'lit' to the solver and pushing a scope
       (and popping the scope before the solver is used for other constraints).
     */
    void add_assumption(expr* lit);

    lbool get_mus(expr_ref_vector& mus);
    
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


#endif
