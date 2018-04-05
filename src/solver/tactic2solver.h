/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic2solver.h

Abstract:

    Wrapper for implementing the external solver interface
    using a tactic.

    This is a light version of the strategic solver.

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#ifndef TACTIC2SOLVER_H_
#define TACTIC2SOLVER_H_

#include "util/params.h"
class ast_manager;
class tactic;
class tactic_factory;
class solver;
class solver_factory;

solver * mk_tactic2solver(ast_manager & m, 
                          tactic * t = nullptr,
                          params_ref const & p = params_ref(), 
                          bool produce_proofs = false, 
                          bool produce_models = true, 
                          bool produce_unsat_cores = false, 
                          symbol const & logic = symbol::null);


solver_factory * mk_tactic2solver_factory(tactic * t);
solver_factory * mk_tactic_factory2solver_factory(tactic_factory * f);

#endif
