/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   smt_induction.h

  Abstract:
   
   Add induction lemmas to context.

  Author:

    Nikolaj Bjorner 2020-04-25
  
--*/

#pragma once

#include "smt/smt_types.h"
#include "ast/rewriter/value_sweep.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

namespace smt {

    class context;

    /**
     * Collect literals that are potentially useful for induction lemmas.
     */
    class collect_induction_literals {
        context&                  ctx;
        ast_manager&              m;
        value_sweep&              vs;        
        unsigned                  m_literal_index;

        literal_vector pre_select();

        void model_sweep_filter(literal_vector& candidates);

    public:
        collect_induction_literals(context& ctx, ast_manager& m, value_sweep& vs);

        literal_vector operator()();               
    };

    /**
     * Synthesize induction lemmas from induction candidates
     */
    class induction_lemmas {
        context&       ctx;
        ast_manager&   m;
        value_sweep&   vs;
        datatype::util m_dt;
        arith_util     m_a;
        recfun::util   m_rec;
        unsigned       m_num_lemmas;

        typedef svector<std::pair<expr*,expr*>> expr_pair_vector;
        typedef std::pair<expr_ref_vector, expr_ref> cond_subst_t;
        typedef vector<cond_subst_t> cond_substs_t;
        typedef std::pair<enode*, unsigned> induction_position_t;
        typedef svector<induction_position_t> induction_positions_t;

        bool viable_induction_sort(sort* s);
        bool viable_induction_parent(enode* p, enode* n);
        bool viable_induction_children(enode* n);
        bool viable_induction_term(enode* p , enode* n);
        enode_vector induction_positions(enode* n);
        induction_positions_t induction_positions2(enode* n);
        void mk_hypothesis_substs(unsigned depth, expr* x, cond_substs_t& subst);
        void mk_hypothesis_substs_rec(unsigned depth, sort* s, expr* y, expr_ref_vector& conds, cond_substs_t& subst);
        void mk_hypothesis_lemma(expr_ref_vector const& conds, expr_pair_vector const& subst, literal alpha);
        void create_hypotheses(unsigned depth, expr_ref_vector const& sks, literal alpha);
        literal mk_literal(expr* e);
        void add_th_lemma(literal_vector const& lits);

    public:
        induction_lemmas(context& ctx, ast_manager& m, value_sweep& vs);

        bool operator()(literal lit);
    };

    /**
     * Establish induction clauses.
     */

    class induction {
        context&     ctx;
        ast_manager& m;
        value_sweep  vs;
        collect_induction_literals m_collect_literals;
        induction_lemmas m_create_lemmas;

        void init_values();

    public:
        induction(context& ctx, ast_manager& m);

        bool operator()();

        static bool should_try(context& ctx);
    };

}
