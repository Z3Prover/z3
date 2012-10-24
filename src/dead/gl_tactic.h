/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    gl_tactic.h

Abstract:

    A T-function/Goldreich Levin-based heuristic.

Author:

    Nikolaj (nbjorner) 2011-12-18

Notes:

--*/

#ifndef _GL_TACTIC_H_
#define _GL_TACTIC_H_

#include"tactic.h"

namespace gl {
    tactic * mk_tactic(ast_manager& m, params_ref const& p);
};

#endif
