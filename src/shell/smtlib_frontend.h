/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_frontend.h

Abstract:

    Smtlib frontend.

Author:

    Leonardo de Moura (leonardo) 2006-11-2.

Revision History:

--*/
#pragma once

unsigned read_smtlib_file(char const * benchmark_file);
unsigned read_smtlib2_commands(char const * command_file);



