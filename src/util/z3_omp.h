/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_omp.h

Abstract:

    Wrapper for OMP functions and data-structures

Author:

    Leonardo (leonardo) 2012-01-05

Notes:

--*/
#ifndef _Z3_OMP_H
#define _Z3_OMP_H

#ifndef _NO_OMP_
#include<omp.h>
#else
#define omp_in_parallel() false
#define omp_set_num_threads(SZ) ((void)0)
#define omp_get_thread_num() 0
#define omp_get_num_procs()  1
#define omp_set_nested(V) ((void)0)
#define omp_init_nest_lock(L) ((void) 0)
#define omp_destroy_nest_lock(L) ((void) 0)
#define omp_set_nest_lock(L) ((void) 0)
#define omp_unset_nest_lock(L) ((void) 0)
struct omp_nest_lock_t {
};
#endif

#endif
