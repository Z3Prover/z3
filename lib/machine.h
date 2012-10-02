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

#ifndef _MACHINE_H_
#define _MACHINE_H_

#ifdef _AMD64_
#define PTR_ALIGNMENT 3
#else
#define PTR_ALIGNMENT 2
#endif

#endif /* _MACHINE_H_ */

