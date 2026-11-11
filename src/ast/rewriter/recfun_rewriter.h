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

#include "ast/datatype_decl_plugin.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/rewriter.h"

class recfun_rewriter {
    ast_manager& m;
    recfun::util  m_rec;
    datatype::util m_dt;
    bool m_recfun_unfold = false;
    unsigned m_max_unfolds;
    unsigned m_num_unfolds = 0;
    obj_hashtable<expr> m_blocked;
    expr_ref_vector m_pinned;

public:
    recfun_rewriter(ast_manager& m, params_ref const& p = params_ref()): m(m), m_rec(m), m_dt(m), m_pinned(m) { updt_params(p); }
    
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

    /**
       \brief Unfolding a recursive definition need not terminate, and rewriting
       is not always subject to resource limits (assertions are simplified before
       check-sat installs them). Every rewrite therefore has a budget of unfoldings.
       inc_unfold charges the budget for unfolding f(args) and returns false when
       the application has to be left alone. Applications that ran into the budget
       are remembered so that later rewrites do not spend the budget on them again.
       reset_unfolds replenishes the budget and is called when a new term is rewritten.
       reset also forgets the remembered applications.
    */
    bool inc_unfold(func_decl* f, unsigned num_args, expr* const* args);
    void reset_unfolds() { m_num_unfolds = 0; }
    void reset() { m_num_unfolds = 0; m_blocked.reset(); m_pinned.reset(); }

    /**
       \brief Check whether the body of the recursive definition of f only uses argument i
       through accessors and recognizers, so that unfolding f on a constructor term at
       position i is structurally decreasing. With allow_any_accessor = false at most one
       accessor kind may be used (guards against reconstructing a non-ground argument);
       with allow_any_accessor = true, which is safe for ground constructor terms, any
       accessor kinds may be used.
    */
    bool is_decreasing_arg(func_decl* f, unsigned i, bool allow_any_accessor);

    /**
       \brief Check whether t is a recursive-function application that can be safely
       evaluated by MBQI because it has a ground, structurally decreasing datatype
       argument and all non-ground arguments have uninterpreted sorts.
    */
    bool is_recfun_with_ground_recursion_args(app* t);

    family_id get_fid() const { return m_rec.get_family_id(); }

    bool is_defined(func_decl* f) const { return m_rec.is_defined(f); }

    void updt_params(params_ref const &p);

};
