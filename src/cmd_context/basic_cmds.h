/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    basic_cmds.h

Abstract:
    Basic commands for SMT2 front end.

Author:

    Leonardo (leonardo) 2011-03-30

Notes:

--*/
#pragma once

class cmd_context;

void install_basic_cmds(cmd_context & ctx);
void install_ext_basic_cmds(cmd_context & ctx);

