/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    timeout.h

Abstract:

    Timeout support

Author:

    Leonardo de Moura (leonardo) 2006-10-02.

Revision History:

--*/
#pragma once

void register_on_timeout_proc(void (*proc)());

void set_timeout(long ms);
void disable_timeout();

