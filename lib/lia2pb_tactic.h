/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    lia2pb_tactic.h

Abstract:

    Reduce bounded LIA benchmark into 0-1 LIA benchmark.

Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Revision History:

--*/
#ifndef _LIA2PB_TACTIC_H_
#define _LIA2PB_TACTIC_H_

#include"params.h"
class ast_manager;
class tactic;

tactic * mk_lia2pb_tactic(ast_manager & m, params_ref const & p = params_ref());

#endif
