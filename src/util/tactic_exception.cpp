/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_exception.cpp

Abstract:

    Tactic expection object.

Author:

    Leonardo (leonardo) 2012-08-15

Notes:

--*/
#include"tactic_exception.h"

char const * tactic_exception::g_tactic_canceled_msg   = "canceled";
char const * tactic_exception::g_tactic_max_memory_msg = "max. memory exceeded";
char const * tactic_exception::g_tactic_max_scopes_msg = "max. scopes exceeded";
char const * tactic_exception::g_tactic_max_steps_msg  = "max. steps exceeded";
char const * tactic_exception::g_tactic_max_frames_msg = "max. frames exceeded";
char const * tactic_exception::g_tactic_no_proofs_msg  = "tactic does not support proof generation";
