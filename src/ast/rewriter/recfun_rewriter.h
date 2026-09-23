/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    recfun_rewriter.h

Abstract:

    Rewriter recursive function applications to values

Author:

    Nikolaj Bjorner (nbjorner) 2020-04-26


--*/

#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/rewriter.h"

class recfun_rewriter {
    ast_manager& m;
    recfun::util  m_rec;
    bool m_recfun_unfold = false;

public:
    recfun_rewriter(ast_manager& m): m(m), m_rec(m) {}
    
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    /**
       \brief Check whether the body of the recursive definition of f only uses argument i
       through accessors and recognizers, so that unfolding f on a constructor term at
       position i is structurally decreasing. With allow_any_accessor = false at most one
       accessor kind may be used (guards against reconstructing a non-ground argument);
       with allow_any_accessor = true, which is safe for ground constructor terms, any
       accessor kinds may be used.
    */
    bool is_decreasing_arg(func_decl* f, unsigned i, bool allow_any_accessor);

    family_id get_fid() const { return m_rec.get_family_id(); }

    void updt_params(params_ref const &p);

};

