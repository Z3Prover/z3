/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    qe_lite.h

Abstract:

    Light weight partial quantifier-elimination procedures 

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-17

Revision History:


--*/

#ifndef __QE_LITE_H__
#define __QE_LITE_H__

#include "ast.h"
#include "uint_set.h"

class qe_lite {
    class impl;
    impl * m_impl;
public:
    qe_lite(ast_manager& m);

    ~qe_lite();

    /**
       \brief
       Apply light-weight quantifier elimination 
       on constants provided as vector of variables. 
       Return the updated formula and updated set of variables that were not eliminated.

    */
    void operator()(app_ref_vector& vars, expr_ref& fml);

    /**
       \brief
       Apply light-weight quantifier elimination to variables present/absent in the index set.
       If 'index_of_bound' is true, then the index_set is treated as the set of
       bound variables. if 'index_of_bound' is false, then index_set is treated as the
       set of variables that are not bound (variables that are not in the index set are bound).
     */
    void operator()(uint_set const& index_set, bool index_of_bound, expr_ref& fml);

    void operator()(uint_set const& index_set, bool index_of_bound, expr_ref_vector& conjs);

    /**
        \brief full rewriting based light-weight quantifier elimination round.
    */
    void operator()(expr_ref& fml, proof_ref& pr);
};

#endif 
