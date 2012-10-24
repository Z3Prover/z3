/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ufbv_strategy.h

Abstract:

    General purpose strategy for UFBV benchmarks.

Author:

    Christoph (cwinter) 2011-07-28

Notes:

--*/
#ifndef _UFBV_STRATEGY_H_
#define _UFBV_STRATEGY_H_

#include"assertion_set_strategy.h"

as_st * mk_ufbv_strategy(ast_manager & m, params_ref const & p);

MK_SIMPLE_ST_FACTORY(ufbv_stf, mk_ufbv_strategy(m, p));

#endif
