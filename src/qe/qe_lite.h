/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qe_lite.h

Abstract:

    Light weight partial quantifier-elimination procedures

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-17

Revision History:


--*/

#ifndef QE_LITE_H_
#define QE_LITE_H_

#include "ast/ast.h"
#include "util/uint_set.h"
#include "util/params.h"

class tactic;

class qe_lite {
    class impl;
    impl * m_impl;
public:
    /** 
        use_array_der controls whether equalities over array reads are simplified
     */
    qe_lite(ast_manager& m, params_ref const & p, bool use_array_der = true);

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

tactic * mk_qe_lite_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("qe-light", "apply light-weight quantifier elimination.", "mk_qe_lite_tactic(m, p)")
*/

#endif
