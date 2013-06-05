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
#ifndef _REL_CONTEXT_H_
#define _REL_CONTEXT_H_
#include "ast.h"
#include "dl_relation_manager.h"
#include "dl_instruction.h"
#include "lbool.h"

namespace datalog {

    class context;
    typedef vector<std::pair<func_decl*,relation_fact> > fact_vector;

    class rel_context {
        context&           m_context;
        ast_manager&       m;
        relation_manager   m_rmanager;
        expr_ref           m_answer;
        relation_base *    m_last_result_relation;
        fact_vector        m_table_facts;
        execution_context  m_ectx;
        instruction_block  m_code;

        class scoped_query;

        void reset_negated_tables();
        
        relation_plugin & get_ordinary_relation_plugin(symbol relation_name);
        
        void reset_tables();

    public:
        rel_context(context& ctx);

        ~rel_context();

        relation_manager & get_rmanager();
        const relation_manager & get_rmanager() const;
        ast_manager& get_manager() const { return m; }
        context&     get_context() const { return m_context; }
        relation_base & get_relation(func_decl * pred); 
        relation_base * try_get_relation(func_decl * pred) const; 
        expr_ref get_last_answer() { return m_answer; }

        bool output_profile() const;

        lbool query(expr* q);
        lbool query(unsigned num_rels, func_decl * const* rels);

        void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                          symbol const * relation_names);
        
        void inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred);

        void set_cancel(bool f);

        /**
           \brief Restrict the set of used predicates to \c res.

           The function deallocates unsused relations, it does not deal with rules.
         */
        void restrict_predicates(func_decl_set const& predicates);


        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f);

        /** \brief add facts to relation
        */
        void add_fact(func_decl* pred, relation_fact const& fact);
        void add_fact(func_decl* pred, table_fact const& fact);

        /** \brief check if facts were added to relation
        */
        bool has_facts(func_decl * pred) const;
        
        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c context object
           takes over the ownership of the relation object.
        */
        void store_relation(func_decl * pred, relation_base * rel);

        void display_output_facts(rule_set const& rules, std::ostream & out) const;
        void display_facts(std::ostream & out) const;

        void display_profile(std::ostream& out);

        lbool saturate();

    };
};

#endif /* _REL_CONTEXT_H_ */
