/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    opt_cmds.h

Abstract:
    Commands for optimization benchmarks

Author:

    Anh-Dung Phan (t-anphan) 2013-10-14

Notes:

--*/
#ifndef OPT_CMDS_H_
#define OPT_CMDS_H_

#include "ast.h"

class cmd_context;

void install_opt_cmds(cmd_context & ctx);


#endif
