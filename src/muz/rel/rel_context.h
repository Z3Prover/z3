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
#ifndef REL_CONTEXT_H_
#define REL_CONTEXT_H_
#include "ast.h"
#include "dl_relation_manager.h"
#include "dl_instruction.h"
#include "dl_engine_base.h"
#include "dl_context.h"
#include "lbool.h"

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

        virtual ~rel_context();

        virtual relation_manager & get_rmanager();
        virtual const relation_manager & get_rmanager() const;
        ast_manager& get_manager() const { return m; }
        context&     get_context() const { return m_context; }
        virtual relation_base & get_relation(func_decl * pred); 
        virtual relation_base * try_get_relation(func_decl * pred) const; 
        virtual bool is_empty_relation(func_decl* pred) const;
        virtual expr_ref try_get_formula(func_decl * pred) const;
        virtual expr_ref get_answer() { return m_answer; }

        virtual bool output_profile() const;

        virtual lbool query(expr* q);
        virtual lbool query(unsigned num_rels, func_decl * const* rels);

        virtual void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                          symbol const * relation_names);
        
        virtual void inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred);

        virtual void collect_statistics(statistics& st) const;

        virtual void updt_params();

        /**
           \brief Restrict the set of used predicates to \c res.

           The function deallocates unsused relations, it does not deal with rules.
         */
        virtual void restrict_predicates(func_decl_set const& predicates);

        virtual void transform_rules();

        virtual bool try_get_size(func_decl* pred, unsigned& rel_size) const;
        /**
           \brief query result if it contains fact.
         */
        virtual bool result_contains_fact(relation_fact const& f);

        virtual void collect_non_empty_predicates(func_decl_set& ps) {
            return get_rmanager().collect_non_empty_predicates(ps);
        }

        /** \brief add facts to relation
        */
        virtual void add_fact(func_decl* pred, relation_fact const& fact);
        virtual void add_fact(func_decl* pred, table_fact const& fact);

        /** \brief check if facts were added to relation
        */
        virtual bool has_facts(func_decl * pred) const;
        
        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c context object
           takes over the ownership of the relation object.
        */
        virtual void store_relation(func_decl * pred, relation_base * rel);

        virtual void display_output_facts(rule_set const& rules, std::ostream & out) const;
        virtual void display_facts(std::ostream & out) const;

        virtual void display_profile(std::ostream& out);

        virtual lbool saturate();

    };
};

#endif /* REL_CONTEXT_H_ */
