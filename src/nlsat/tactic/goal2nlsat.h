/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal2nlsat.h

Abstract:

    "Compile" a goal into the nonlinear arithmetic engine.
    Non-arithmetic atoms are "abstracted" into boolean variables.
    Non-supported terms are "abstracted" into variables.

    The mappings can be used to convert back the state of the 
    engine into a goal.

Author:

    Leonardo (leonardo) 2012-01-02

Notes:

--*/
#ifndef GOAL2NLSAT_H_
#define GOAL2NLSAT_H_

#include"nlsat_types.h"
#include"model_converter.h"

class goal;
class expr2var;

class goal2nlsat {
    struct imp;
    imp *  m_imp;
    struct scoped_set_imp;
public:
    goal2nlsat();
    ~goal2nlsat();
    
    static void collect_param_descrs(param_descrs & r);
    
    /**
       \brief "Compile" the goal into the given nlsat engine.
       Store a mapping from atoms to boolean variables into a2b.
       Store a mapping from terms into arithmetic variables into t2x.
       
       \remark a2b and t2x m don't need to be empty. The definitions there are reused.

       The input is expected to be in CNF
    */
    void operator()(goal const & g, params_ref const & p, nlsat::solver & s, expr2var & a2b, expr2var & t2x);
    
};

class nlsat2goal {
    struct imp;
    imp *  m_imp;
public:
    nlsat2goal(ast_manager& m);
    ~nlsat2goal();

    static void collect_param_descrs(param_descrs & r);

    /**
       \brief Translate a literal into a formula.
    */   
    expr_ref operator()(nlsat::solver& s, u_map<expr*> const& b2a, u_map<expr*> const& x2t, nlsat::literal l);

};

#endif
