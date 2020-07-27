/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    nnf.h

Abstract:

    Negation Normal Form & Skolemization

Author:

    Leonardo (leonardo) 2008-01-11

Notes:
    Major revision on 2011-10-06

--*/
#pragma once

#include "ast/ast.h"
#include "util/params.h"
#include "ast/normal_forms/defined_names.h"

class nnf {
    struct imp;
    imp *  m_imp;
public:
    nnf(ast_manager & m, defined_names & n, params_ref const & p = params_ref());
    ~nnf();
    
    void operator()(expr * n,                          // [IN] expression that should be put into NNF
                    expr_ref_vector & new_defs,        // [OUT] new definitions
                    proof_ref_vector & new_def_proofs, // [OUT] proofs of the new definitions 
                    expr_ref & r,                      // [OUT] resultant expression
                    proof_ref & p                      // [OUT] proof for (~ n r)
                    );

    void updt_params(params_ref const & p);
    /*
      REG_MODULE_PARAMS('nnf', 'nnf::get_param_descrs')
    */
    static void get_param_descrs(param_descrs & r);

    void reset();
    void reset_cache();
};

