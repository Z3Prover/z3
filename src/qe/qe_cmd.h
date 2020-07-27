/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    qe_cmd.h

Abstract:
    SMT2 front-end 'qe' command.

Author:

    Nikolaj Bjorner (nbjorner) 2011-01-11

Notes:

--*/
#pragma once

class cmd_context;

void install_qe_cmd(cmd_context & ctx, char const * cmd_name = "elim-quantifiers");

