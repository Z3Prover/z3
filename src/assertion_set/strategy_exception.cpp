/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    strategy_exception.cpp

Abstract:

    Strategy exception

Author:

    Leonardo (leonardo) 2011-05-02

Notes:

--*/
#include"strategy_exception.h"

char const * strategy_exception::g_ste_canceled_msg   = "canceled";
char const * strategy_exception::g_ste_max_memory_msg = "max. memory exceeded";
char const * strategy_exception::g_ste_max_scopes_msg = "max. scopes exceeded";
char const * strategy_exception::g_ste_max_steps_msg  = "max. steps exceeded";
char const * strategy_exception::g_ste_max_frames_msg = "max. frames exceeded";
char const * strategy_exception::g_ste_no_proofs_msg  = "strategy does not support proof generation";
