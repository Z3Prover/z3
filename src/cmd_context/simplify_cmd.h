/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    simplify_cmd.h

Abstract:
    SMT2 front-end 'simplify' command.

Author:

    Leonardo (leonardo) 2011-04-20

Notes:

--*/
#pragma once

class cmd_context;

void install_simplify_cmd(cmd_context & ctx, char const * cmd_name = "simplify");

