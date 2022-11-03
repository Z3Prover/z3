/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    extract_eqs.h

Abstract:

    simplifier for solving equations

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.

--*/


#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "util/scoped_ptr_vector.h"


namespace euf {

    struct dependent_eq {
        app* var;
        expr_ref term;
        expr_dependency* dep;
        dependent_eq(app* var, expr_ref const& term, expr_dependency* d) : var(var), term(term), dep(d) {}
    };

    typedef vector<dependent_eq> dep_eq_vector;

    class extract_eq {
    public:
        virtual ~extract_eq() {}
        virtual void get_eqs(dependent_expr const& e, dep_eq_vector& eqs) = 0;
        virtual void pre_process(dependent_expr_state& fmls) {}
        virtual void updt_params(params_ref const& p) {}
    };

    void register_extract_eqs(ast_manager& m, scoped_ptr_vector<extract_eq>& ex);

}
