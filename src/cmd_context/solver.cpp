/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    solver.h

Abstract:

    abstract solver interface

Author:

    Leonardo (leonardo) 2011-03-19

Notes:

--*/
#include"solver.h"

unsigned solver::get_num_assertions() const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

expr * solver::get_assertion(unsigned idx) const {
    NOT_IMPLEMENTED_YET();
    return 0;
}

void solver::display(std::ostream & out) const {
    out << "(solver)";
}

