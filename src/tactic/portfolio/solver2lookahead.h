/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    solver2lookahead.h

Abstract:

    Lookahead wrapper for arbitrary solver.

Author:

    Nikolaj Bjorner (nbjorner) 2017-10-9

Notes:
   
--*/
#ifndef SOLVER2LOOKAHEAD_H_
#define SOLVER2LOOKAHEAD_H_

class solver;

solver * mk_solver2lookahead(solver* s);

#endif
