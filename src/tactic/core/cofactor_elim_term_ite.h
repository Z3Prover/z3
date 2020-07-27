/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cofactor_elim_term_ite.h

Abstract:

    Eliminate (ground) term if-then-else's using cofactors.

Author:

    Leonardo de Moura (leonardo) 2011-06-05.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"

class cofactor_elim_term_ite {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    cofactor_elim_term_ite(ast_manager & m, params_ref const & p = params_ref());
    virtual ~cofactor_elim_term_ite();

    void updt_params(params_ref const & p);
    void collect_param_descrs(param_descrs & r);

    void operator()(expr * t, expr_ref & r);
    
    void cleanup();

};

