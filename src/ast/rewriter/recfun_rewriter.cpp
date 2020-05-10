/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    recfun_rewriter.cpp

Abstract:

    Rewriter recursive function applications to values

Author:

    Nikolaj Bjorner (nbjorner) 2020-04-26


--*/


#include "ast/rewriter/recfun_rewriter.h"
#include "ast/rewriter/var_subst.h"
    
br_status recfun_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (m_rec.is_defined(f) && num_args > 0) {
        for (unsigned i = 0; i < num_args; ++i) {
            if (!m.is_value(args[i]))
                return BR_FAILED;
        }
        if (!m_rec.has_def(f))
            return BR_FAILED;
        recfun::def const& d = m_rec.get_def(f);
        if (!d.get_rhs())
            return BR_FAILED;
        var_subst sub(m);
        result = sub(d.get_rhs(), num_args, args);
        return BR_REWRITE_FULL;
    }
    else {
        return BR_FAILED;
    }
}


