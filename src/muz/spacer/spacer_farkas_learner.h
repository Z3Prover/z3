/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_farkas_learner.h

Abstract:

    SMT2 interface for the datalog SPACER

Author:

    Krystof Hoder (t-khoder) 2011-11-1.

Revision History:

--*/

#ifndef _SPACER_FARKAS_LEARNER_H_
#define _SPACER_FARKAS_LEARNER_H_

#include "ast/ast.h"

namespace spacer {

class farkas_learner {
    typedef obj_hashtable<expr> expr_set;

    bool m_split_literals;

    void combine_constraints(unsigned cnt, app * const * constrs, rational const * coeffs, expr_ref& res);

    bool is_farkas_lemma(ast_manager& m, expr* e);

    void get_asserted(proof* p, expr_set const& bs, ast_mark& b_closed, obj_hashtable<expr>& lemma_set, expr_ref_vector& lemmas);

    bool is_pure_expr(func_decl_set const& symbs, expr* e, ast_manager& m) const;

public:
    farkas_learner(): m_split_literals(false) {}

    /**
        Traverse a proof and retrieve lemmas using the vocabulary from bs.
    */
    void get_lemmas(proof* root, expr_set const& bs, expr_ref_vector& lemmas);

    void collect_statistics(statistics& st) const {}
    void reset_statistics() {}


    /** \brief see smt::farkas_util::set_split_literals */
    void set_split_literals(bool v) {m_split_literals = v;}

};


}

#endif
