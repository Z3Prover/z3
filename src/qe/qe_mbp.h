/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qe_mbp.h

Abstract:

    Model-based projection utilities

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#ifndef __QE_MBP_H__
#define __QE_MBP_H__

#include "ast.h"
#include "params.h"

class qe_mbp {
    class impl;
    impl * m_impl;
public:
    qe_mbp(ast_manager& m);

    ~qe_mbp();

    /**
       \brief
       Apply model-based qe on constants provided as vector of variables. 
       Return the updated formula and updated set of variables that were not eliminated.

    */
    void operator()(app_ref_vector& vars, model_ref& mdl, expr_ref& fml);

    /**
        \brief full rewriting based light-weight quantifier elimination round.
    */
    void operator()(expr_ref& fml, proof_ref& pr);

    void set_cancel(bool f);
};

#endif 
