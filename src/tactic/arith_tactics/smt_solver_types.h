/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt_solver_types.h

Abstract:

    Auxiliary definitions for smt::solver class.
    
Author:

    Leonardo de Moura (leonardo) 2011-06-25.

Revision History:
    This was an experiment to rewrite Z3 kernel.
    It will be deleted after we finish revamping Z3 kernel.

--*/
#ifndef _SMT_SOLVER_TYPES_H_
#define _SMT_SOLVER_TYPES_H_

#include"assertion_set.h"
#include"strategy_exception.h"
#include"params.h"
#include"statistics.h"
#include"lbool.h"
#include"sat_types.h"

class ast_translation;

namespace sat {
    class solver;
};

namespace smt {
    class solver_exp;
    class formula_compiler;
    typedef unsigned atom_id;
    typedef unsigned_vector atom_id_vector;
    const atom_id null_atom_id = sat::null_bool_var;
};

MK_ST_EXCEPTION(smt_solver_exception);

#endif
