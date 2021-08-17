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

#include "util/hash.h"
#include "util/hashtable.h"
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
        typedef svector<std::pair<expr*,expr*>> expr_pair_vector;
        typedef std::pair<expr_ref_vector, expr_ref> cond_subst_t;
        typedef vector<cond_subst_t> cond_substs_t;
        typedef std::pair<enode*, unsigned> induction_position_t;
        typedef svector<induction_position_t> induction_positions_t;
        typedef vector<induction_positions_t> induction_combinations_t;
        struct induction_term_and_position_t {
            expr*                 m_term;
            induction_positions_t m_positions;
            ptr_vector<expr>      m_skolems;
            induction_term_and_position_t(): m_term(nullptr) {}
            induction_term_and_position_t(expr* t, induction_positions_t const& p):
                m_term(t), m_positions(p) {}
        };
        struct it_hash {
            unsigned operator()(induction_term_and_position_t const& t) const {
                unsigned a = get_node_hash(t.m_term);
                for (auto const& p : t.m_positions) {
                    a = mk_mix(a, p.second, get_node_hash(p.first->get_expr()));
                }
                return a;
            }
        };

        struct it_eq {
            bool operator()(induction_term_and_position_t const& s, induction_term_and_position_t const& t) const {
                if (s.m_term != t.m_term || s.m_positions.size() != t.m_positions.size())
                    return false;
                for (unsigned i = s.m_positions.size(); i-- > 0; ) {
                    auto const& p1 = s.m_positions[i];
                    auto const& p2 = t.m_positions[i];
                    if (p1.first != p2.first || p1.second != p2.second)
                        return false;
                }
                return true;
            }
        };

        context&       ctx;
        ast_manager&   m;
        datatype::util m_dt;
        arith_util     m_a;
        recfun::util   m_rec;
        unsigned       m_num_lemmas;

        unsigned        m_ts {0};
        unsigned_vector m_marks;
        vector<ptr_vector<app>> m_depth2terms;

        expr_ref_vector                                          m_trail;
        hashtable<induction_term_and_position_t, it_hash, it_eq> m_skolems;


        bool viable_induction_sort(sort* s);
        bool viable_induction_parent(enode* p, enode* n);
        bool viable_induction_children(enode* n);
        bool viable_induction_term(enode* p , enode* n);
        enode_vector induction_positions(enode* n);
        induction_positions_t induction_positions2(enode* n);
        void initialize_levels(enode* n);
        induction_combinations_t induction_combinations(enode* n);
        bool positions_dont_overlap(induction_positions_t const& p);
        void mk_hypothesis_substs(unsigned depth, expr* x, cond_substs_t& subst);
        void mk_hypothesis_substs_rec(unsigned depth, sort* s, expr* y, expr_ref_vector& conds, cond_substs_t& subst);
        void mk_hypothesis_lemma(expr_ref_vector const& conds, expr_pair_vector const& subst, literal alpha);
        void create_hypotheses(unsigned depth, expr_ref_vector const& sks, literal alpha);
        literal mk_literal(expr* e);
        void add_th_lemma(literal_vector const& lits);
        void apply_induction(literal lit, induction_positions_t const & positions);

    public:
        induction_lemmas(context& ctx, ast_manager& m);

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
