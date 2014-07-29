/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    bcd2.h

Abstract:

    Bcd2 based MaxSAT.

Author:

    Nikolaj Bjorner (nbjorner) 2014-4-17

Notes:

--*/

#ifndef _BCD2_H_
#define _BCD2_H_

#include "maxsmt.h"

namespace opt {
    maxsmt_solver_base* mk_bcd2(ast_manager& m, opt_solver* s, params_ref& p, 
                                 vector<rational> const& ws, expr_ref_vector const& soft);
}
#endif
