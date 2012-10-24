/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfuf_tactic.h

Abstract:

    Tactic for QF_QFUF benchmarks.

Author:

    Leonardo de Moura (leonardo) 2012-02-21


Notes:

--*/
#ifndef _QFUF_TACTIC_
#define _QFUF_TACTIC_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_qfuf_tactic(ast_manager & m, params_ref const & p);

#endif
