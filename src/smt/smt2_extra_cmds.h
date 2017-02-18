/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2_extra_cmds.h

Abstract:

    Additional SMT-specific commands.

Author:

    Christoph (cwinter) 2017-01-16

Notes:

--*/
#ifndef SMT2_EXTRA_CMDS_H_
#define SMT2_EXTRA_CMDS_H_

class cmd_context;

void install_smt2_extra_cmds(cmd_context & ctx);

#endif /* SMT2_EXTRA_CMDS_H_ */
