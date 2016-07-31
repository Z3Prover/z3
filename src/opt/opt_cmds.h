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
#include "opt_context.h"

class cmd_context;

void install_opt_cmds(cmd_context & ctx, opt::context* opt = 0);


#endif
