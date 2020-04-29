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
    class create_induction_lemmas {
        context&     ctx;
        ast_manager& m;
        value_sweep& vs;
        datatype::util m_dt;
        obj_map<sort, func_decl*> m_sort2skolem;
        ast_ref_vector m_pinned;
        unsigned m_num_lemmas;

        typedef svector<std::pair<expr*,expr*>> expr_pair_vector;

        func_decl* mk_skolem(sort* s);

        struct abstraction {
            expr_ref          m_term;
            expr_pair_vector m_eqs;
            abstraction(expr_ref& e): m_term(e) {}
            abstraction(ast_manager& m, expr* e, expr* n1, expr* n2): m_term(e, m) {
                if (n1 != n2) m_eqs.push_back(std::make_pair(n1, n2));
            }
            abstraction(ast_manager& m, expr* e, expr_pair_vector const& eqs): 
                m_term(e, m), m_eqs(eqs) {
            }
            
        };
        typedef vector<abstraction> abstractions;
        
        struct abstraction_arg {
            expr_ref_vector   m_terms;
            expr_pair_vector m_eqs;
            abstraction_arg(ast_manager& m): m_terms(m) {}
            void push_back(abstraction& a) {
                m_terms.push_back(a.m_term);
                m_eqs.append(a.m_eqs);
            }
        };
        typedef vector<abstraction_arg> abstraction_args;

        bool is_induction_candidate(enode* n);
        enode_vector induction_positions(enode* n);
        void abstract(enode* n, enode* t, expr* x, abstractions& result);
        void filter_abstractions(bool sign, abstractions& abs);
        void create_lemmas(expr* t, expr* sk, abstraction& a, literal lit);
        literal mk_literal(expr* e);
        void add_th_lemma(literal_vector const& lits);

    public:
        create_induction_lemmas(context& ctx, ast_manager& m, value_sweep& vs);

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
        create_induction_lemmas m_create_lemmas;

        void init_values();

    public:
        induction(context& ctx, ast_manager& m);

        bool operator()();

        static bool should_try(context& ctx);
    };

}
