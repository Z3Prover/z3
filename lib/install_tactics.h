/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    install_tactics.h

Abstract:
    Install tactics in the SMT 2.0 frontend.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef _INSTALL_TACTICS_H_
#define _INSTALL_TACTICS_H_

class tactic_manager;
void install_tactics(tactic_manager & ctx);

#endif
