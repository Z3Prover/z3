/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    preprocessor_params.h

Abstract:

    Preprocess AST before adding them to the logical context

Author:

    Leonardo de Moura (leonardo) 2012-12-02.

Revision History:

--*/
#include"preprocessor_params.h"
#include"smt_params_helper.hpp"

void preprocessor_params::updt_local_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_macro_finder            = p.macro_finder();
    m_pull_nested_quantifiers = p.pull_nested_quantifiers();
    m_refine_inj_axiom        = p.refine_inj_axioms();
}

void preprocessor_params::updt_params(params_ref const & p) {
    pattern_inference_params::updt_params(p);
    bv_simplifier_params::updt_params(p);
    arith_simplifier_params::updt_params(p);
    updt_local_params(p);
}
