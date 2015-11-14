/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_solver_old.cpp

Abstract:
    OLD API for using solvers.

    This has been deprecated

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"


void Z3_display_statistics(Z3_context c, std::ostream& s) {
    mk_c(c)->get_smt_kernel().display_statistics(s);
}

void Z3_display_istatistics(Z3_context c, std::ostream& s) {
    mk_c(c)->get_smt_kernel().display_istatistics(s);
}

