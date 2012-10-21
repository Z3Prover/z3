/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dl_cmds.h

Abstract:
    Datalog commands for SMT2 front-end.

Author:

    Leonardo (leonardo) 2011-03-28

Notes:

--*/
#ifndef _DL_CMDS_H_
#define _DL_CMDS_H_

class cmd;
class cmd_context;

void install_dl_cmds(cmd_context & ctx);

namespace datalog {

    class context;

    /**
    Create a command for declaring relations which is connected to 
    a particular datalog context.

    Caller must ensure the returned object is deallocated (e.g. by passing it to a cmd_context).
    */
    cmd * mk_declare_rel_cmd(context& dctx);

    /**
       Declare a constant as a universal/existential variable.
       It is implicitly existentially or universally quantified
       by the rules.
    */
    cmd * mk_declare_var_cmd(context& dctx);

}

#endif
