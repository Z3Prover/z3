/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    machine.h

Abstract:

    Machine/OS dependent configuration

Author:

    Leonardo de Moura (leonardo) 2006-09-13.

Revision History:

--*/

#pragma once

#if defined(__LP64__) || defined(_WIN64)
#define PTR_ALIGNMENT 3
#else
#define PTR_ALIGNMENT 2
#endif


