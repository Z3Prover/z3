/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_explanations.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-11-08.

Revision History:

--*/

#ifndef DL_MK_EXPLANATIONS_H_
#define DL_MK_EXPLANATIONS_H_

#include "dl_context.h"
#include "dl_rule_transformer.h"

namespace datalog {

    class explanation_relation;
    class explanation_relation_plugin;

    class mk_explanations : public rule_transformer::plugin {

        typedef obj_map<func_decl, func_decl *> decl_map;

        ast_manager &  m_manager;
        context &      m_context;
        dl_decl_util & m_decl_util;
        bool           m_relation_level;
        ast_ref_vector m_pinned;
        explanation_relation_plugin * m_er_plugin;
        sort *         m_e_sort;
        scoped_rel<explanation_relation> m_e_fact_relation;

        decl_map m_e_decl_map;

        symbol get_rule_symbol(rule * r);

        app * get_e_lit(app * lit, unsigned e_var_idx);
        rule * get_e_rule(rule * r);

        /**
           If \c m_relation_level is true, ensure \c e_decl predicate will be represented by 
           the right relation object. \c orig is the predicate corresponding to \c e_decl without
           the explanation column.
        */
        void assign_rel_level_kind(func_decl * e_decl, func_decl * orig);
        void translate_rel_level_relation(relation_manager & rmgr, relation_base & orig, relation_base & e_rel);

        void transform_rules(const rule_set & src, rule_set & dst);
        
        void transform_facts(relation_manager & rmgr, rule_set const& src, rule_set& dst);
    public:
        /**
           If relation_level is true, the explanation will not be stored for each fact,
           but we will rather store history of the whole relation.
        */
        mk_explanations(context & ctx);

        /**
           \brief Return explanation predicate that corresponds to \c orig_decl.
        */
        func_decl * get_e_decl(func_decl * orig_decl);

        static func_decl * get_union_decl(context & ctx);
        func_decl * get_union_decl() const {
            return get_union_decl(m_context);
        }

        rule_set * operator()(rule_set const & source);

        static expr* get_explanation(relation_base const& r);
    };
};

#endif /* DL_MK_EXPLANATIONS_H_ */

