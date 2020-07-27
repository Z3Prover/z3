/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    cmd_context_to_goal.h

Abstract:
    Procedure for copying the assertions in the
    command context to a goal object.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:

--*/
#pragma once

void assert_exprs_from(cmd_context const & ctx, goal & t);

