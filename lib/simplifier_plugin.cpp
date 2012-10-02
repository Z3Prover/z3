/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    simplifier_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-29.

Revision History:

--*/
#include"simplifier_plugin.h"

/**
   \brief Copy every args[i] mult[i] times to new_args.
*/
void expand_args(unsigned num_args, rational const * mults, expr * const * args, ptr_buffer<expr> & new_args) {
    for (unsigned i = 0; i < num_args; i++) {
        rational const & c = mults[i];
        SASSERT(c.is_int());
        rational j(0);
        while (j < c) {
            new_args.push_back(args[i]);
            j++;
        }
    }
}

bool simplifier_plugin::reduce(func_decl * f, unsigned num_args, rational const * mults, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    if (f->is_idempotent()) {
        return reduce(f, num_args, args, result);
    }
    else {
        ptr_buffer<expr> new_args;
        expand_args(num_args, mults, args, new_args);
        return reduce(f, new_args.size(), new_args.c_ptr(), result);
    }
}
