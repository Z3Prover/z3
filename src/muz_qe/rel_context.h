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
#include "lbool.h"

namespace datalog {

    class context;

    class rel_context {
        typedef vector<std::pair<func_decl*,relation_fact> > fact_vector;

        context&           m_context;
        ast_manager&       m;
        relation_manager   m_rmanager;
        expr_ref           m_answer;
        volatile bool      m_cancel;
        relation_base *    m_last_result_relation;
        decl_set           m_output_preds;
        fact_vector        m_table_facts;

        void reset_negated_tables();
        
        relation_plugin & get_ordinary_relation_plugin(symbol relation_name);
        
        void reset_tables();

    public:
        rel_context(context& ctx);

        ~rel_context();

        relation_manager & get_rmanager();
        const relation_manager & get_rmanager() const;
        ast_manager& get_manager() { return m; }
        context&     get_context() { return m_context; }
        relation_base & get_relation(func_decl * pred); 
        relation_base * try_get_relation(func_decl * pred) const; 
        expr_ref get_last_answer() { return m_answer; }

        bool output_profile() const;


        lbool query(expr* q);
        lbool query(unsigned num_rels, func_decl * const* rels);

        void set_predicate_representation(func_decl * pred, unsigned relation_name_cnt, 
                                          symbol const * relation_names);
        
        void inherit_predicate_kind(func_decl* new_pred, func_decl* orig_pred);

        void cancel() { m_cancel = true; }
        
        void cleanup() { m_cancel = false; }


        /**
           \brief Restrict the set of used predicates to \c res.

           The function deallocates unsused relations, it does not deal with rules.
         */
        void restrict_predicates(const decl_set & res);

        void collect_predicates(decl_set & res);        

        void set_output_predicate(func_decl * pred);
        bool is_output_predicate(func_decl * pred) { return m_output_preds.contains(pred); }
        const decl_set & get_output_predicates() const { return m_output_preds; }


        /**
           \brief query result if it contains fact.
         */
        bool result_contains_fact(relation_fact const& f);

        void add_fact(func_decl* pred, relation_fact const& fact);

        void add_fact(func_decl* pred, table_fact const& fact);
        
        /**
           \brief Store the relation \c rel under the predicate \c pred. The \c context object
           takes over the ownership of the relation object.
        */
        void store_relation(func_decl * pred, relation_base * rel);

        void display_output_facts(std::ostream & out) const;
        void display_facts(std::ostream & out) const;

        lbool saturate();

    };
};

#endif /* _REL_CONTEXT_H_ */
