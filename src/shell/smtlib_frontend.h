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
#ifndef _SMTLIB_FRONTEND_H_
#define _SMTLIB_FRONTEND_H_

#include"front_end_params.h"

unsigned read_smtlib_file(char const * benchmark_file, front_end_params & front_end_params);

unsigned read_smtlib_commands(char const* command_file, front_end_params& front_end_params);
unsigned read_smtlib2_commands(char const* command_file, front_end_params& front_end_params);

#ifdef _Z3_BUILD_PARALLEL_MPI
unsigned start_mpi_subordinate(front_end_params& front_end_params);
#endif

#endif /* _SMTLIB_FRONTEND_H_ */


