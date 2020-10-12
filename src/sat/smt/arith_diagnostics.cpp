/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_diagnostics.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    
    std::ostream& solver::display(std::ostream& out) const { return out; }
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const { return out;}
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const { return out;}
    void solver::collect_statistics(statistics& st) const {}
}
