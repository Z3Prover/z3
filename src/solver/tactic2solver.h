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
#pragma once

#include "util/params.h"

class ast_manager;
class tactic;
class solver;
class solver_factory;

typedef tactic* (*tactic_factory)(ast_manager&, const params_ref&);

solver * mk_tactic2solver(ast_manager & m, 
                          tactic * t = nullptr,
                          params_ref const & p = params_ref(), 
                          bool produce_proofs = false, 
                          bool produce_models = true, 
                          bool produce_unsat_cores = false, 
                          symbol const & logic = symbol::null);


solver_factory * mk_tactic2solver_factory(tactic * t);
solver_factory * mk_tactic_factory2solver_factory(tactic_factory f);

