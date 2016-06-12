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

std::ostream& solver::display(std::ostream & out) const {
    return out << "(solver)";
}

void solver::get_assertions(expr_ref_vector& fmls) const {
    unsigned sz = get_num_assertions();
    for (unsigned i = 0; i < sz; ++i) {
        fmls.push_back(get_assertion(i));
    }
}
