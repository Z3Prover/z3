/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_farkas_learner.h

Abstract:

    SMT2 interface for the datalog PDR

Author:

    Krystof Hoder (t-khoder) 2011-11-1.

Revision History:

--*/

#ifndef _PDR_FARKAS_LEARNER_H_
#define _PDR_FARKAS_LEARNER_H_

#include "arith_decl_plugin.h"
#include "ast_translation.h"
#include "bv_decl_plugin.h"
#include "smt_kernel.h"
#include "bool_rewriter.h"
#include "pdr_util.h"
#include "smt_params.h"
#include "tactic.h"

namespace pdr {

class farkas_learner {
    class farkas_collector;
    class constant_replacer_cfg;
    class equality_expander_cfg;
    class constr;

    typedef obj_hashtable<expr> expr_set;

    smt_params               m_proof_params;
    ast_manager              m_pr;
    scoped_ptr<smt::kernel>  m_ctx;
    constr*                  m_constr;

    // 
    // true:  produce a combined constraint by applying Farkas coefficients.
    // false: produce a conjunction of the negated literals from the theory lemmas.
    //
    bool                     m_combine_farkas_coefficients; 


    static smt_params get_proof_params(smt_params& orig_params);

    //
    // all ast objects passed to private functions have m_proof_mgs as their ast_manager
    //

    ast_translation p2o;       /** Translate expression from inner ast_manager to outer one */
    ast_translation o2p;       /** Translate expression from outer ast_manager to inner one */


    /** All ast opbjects here are in the m_proof_mgs */
    void get_lemma_guesses_internal(proof * p, expr* A, expr * B, expr_ref_vector& lemmas);

    bool farkas2lemma(proof * fstep, expr* A, expr * B, expr_ref& res);

    void combine_constraints(unsigned cnt, app * const * constrs, rational const * coeffs, expr_ref& res);

    bool try_ensure_lemma_in_language(expr_ref& lemma, expr* A, const func_decl_set& lang);

    bool is_farkas_lemma(ast_manager& m, expr* e);
   
    void get_asserted(proof* p, expr_set const& bs, ast_mark& b_closed, obj_hashtable<expr>& lemma_set, expr_ref_vector& lemmas);

    bool is_pure_expr(func_decl_set const& symbs, expr* e) const;

    static void test();

public:
    farkas_learner(smt_params& params, ast_manager& m);

    ~farkas_learner();

    /**
       All ast objects have the ast_manager which was passed as 
       an argument to the constructor (i.e. m_outer_mgr)
       
       B is a conjunction of literals.
       A && B is unsat, equivalently A => ~B is valid
       Find a weakened B' such that
       A && B' is unsat and B' uses vocabulary (and constants) in common with A.
       return lemmas to weaken B.     
    */

    bool get_lemma_guesses(expr * A, expr * B, expr_ref_vector& lemmas);

    /**
        Traverse a proof and retrieve lemmas using the vocabulary from bs.
    */
    void get_lemmas(proof* root, expr_set const& bs, expr_ref_vector& lemmas);

    /**
       Traverse a proof and retrieve consequences of A that are used to establish ~B.
       The assumption is that:

          A => \/ ~consequences[i]  and  \/ ~consequences[i] => ~B

       e.g., the second implication can be rewritten as:

          B => /\ consequences[i]
     */
    void get_consequences(proof* root, expr_set const& bs, expr_ref_vector& consequences);

    /**
       \brief Simplify lemmas using subsumption.
     */
    void simplify_lemmas(expr_ref_vector& lemmas);

    void collect_statistics(statistics& st) const;

};


}

#endif
