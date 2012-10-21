/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dbg_cmds.h

Abstract:
    SMT2 front-end commands for debugging purposes.

Author:

    Leonardo (leonardo) 2011-04-01

Notes:

--*/
#ifndef _DBG_CMDS_H_
#define _DBG_CMDS_H_

class cmd_context;

void install_dbg_cmds(cmd_context & ctx);

#endif
