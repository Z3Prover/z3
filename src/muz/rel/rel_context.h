/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    rel_context.h

Abstract:

    context for relational datalog engine.

Author:

    Nikolaj Bjorner (nbjorner) 2012-12-3.

Revision History:

    Extracted from dl_context

--*/
#pragma once
#include "ast/ast.h"
#include "muz/rel/dl_relation_manager.h"
#include "muz/rel/dl_instruction.h"
#include "muz/base/dl_engine_base.h"
#include "muz/base/dl_context.h"
#include "util/lbool.h"

namespace datalog {

    class context;
    typedef vector<std::pair<func_decl*,relation_fact> > fact_vector;

    class rel_context : public rel_context_base {
        context&           m_context;
        ast_manager&       m;
        relation_manager   m_rmanager;
        expr_ref           m_answer;
        relation_base *    m_last_result_relation;
        fact_vector        m_table_facts;
        execution_context  m_ectx;
        instruction_block  m_code;
        double             m_sw;

        class scoped_query;

        void reset_negated_tables();
        
        relation_plugin & get_ordinary_relation_plugin(symbol relation_name);
        
        lbool saturate(scoped_query& sq);

        void setup_default_relation();

    public:
        rel_context(context& ctx);

        ~rel_context() override;

        relation_manager & get_rmanager() override;
        const relation_manager & get_rmanager() const override;
        ast_manager& get_manager() const { return m; }
        context&     get_context() const { return m_context; }
        relation_base & get_relation(func_decl * pred) override;
        relation_base * try_get_relation(func_decl * pred) const override;
        bool is_empty_relation(func_decl* pred) const override;
        expr_ref try_get_formula(func_decl * pred) const override;
        expr_ref get_answer() override { return m_answer; }

        bool output_profile() const override;

        lbool query(expr* q) override;
        lbool query(unsigned num_rels, func_decl * const* rels) override;

        void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                          symbol const * relation_names) override;
        
        void inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred) override;

        void collect_statistics(statistics& st) const override;

        void updt_params() override;

        /**
           \brief Restrict the set of used predicates to \c res.

           The function deallocates unused relations, it does not deal with rules.
         */
        void restrict_predicates(func_decl_set const& predicates) override;

        void transform_rules() override;

        model_ref get_model() override;

        bool try_get_size(func_decl* pred, unsigned& rel_size) const override;
        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f) override;

        void collect_non_empty_predicates(func_decl_set& ps) override {
            return get_rmanager().collect_non_empty_predicates(ps);
        }

        /** \brief add facts to relation
        */
        void add_fact(func_decl* pred, relation_fact const& fact) override;
        void add_fact(func_decl* pred, table_fact const& fact) override;

        /** \brief check if facts were added to relation
        */
        bool has_facts(func_decl * pred) const override;
        
        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c context object
           takes over the ownership of the relation object.
        */
        void store_relation(func_decl * pred, relation_base * rel) override;

        void display_output_facts(rule_set const& rules, std::ostream & out) const override;
        void display_facts(std::ostream & out) const override;

        void display_profile(std::ostream& out) override;

        lbool saturate() override;

    };
};

