/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers2.h

Abstract:

    Replace universal quantifiers over interpreted predicates in the body
    by instantiations mined using bounded model checking search.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/
#ifndef _DL_MK_EXTRACT_QUANTIFIERS2_H_
#define _DL_MK_EXTRACT_QUANTIFIERS2_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"obj_pair_hashtable.h"

namespace datalog {

    /**
       \brief Extract universal quantifiers from rules.
    */
    class mk_extract_quantifiers2 : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        func_decl_ref   m_query_pred;
        quantifier_ref_vector   m_quantifiers;
        ptr_vector<rule>        m_qrules;
        vector<expr_ref_vector>m_bindings;
        vector<vector<expr_ref_vector> > m_rule_bindings;
        vector<vector<expr_ref_vector> > m_quantifier_bindings;
        obj_pair_map<rule,quantifier, expr_ref_vector*> m_quantifier_instantiations;
        obj_map<rule, obj_hashtable<expr>*>  m_seen;
        
        bool                    m_has_quantifiers;
        obj_map<expr,expr*>     m_map;
        expr_ref_vector         m_refs;

        class instance_plugin;

        void reset();

        void extract(rule& r, rule_set& new_rules);

        void apply(rule& r, rule_set& new_rules);

        app_ref ensure_app(expr* e);

        bool matches_signature(func_decl* head, expr_ref_vector const& binding);

        bool matches_quantifier(quantifier* q, expr_ref_vector const& binding);

        void match_bindings(unsigned i, unsigned j, unsigned k);

        bool mk_abstract_expr(expr_ref& term);

        bool mk_abstract_binding(expr_ref_vector const& binding, expr_ref_vector& result);

        void mk_abstraction_map(rule& r, expr_ref_vector const& binding);

    public:
        /**
           \brief Create rule transformer that extracts universal quantifiers (over recursive predicates).
         */
        mk_extract_quantifiers2(context & ctx);

        virtual ~mk_extract_quantifiers2();

        void set_query(func_decl* q);
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc);

        bool has_quantifiers() { return m_has_quantifiers; }

    };

};

#endif /* _DL_MK_EXTRACT_QUANTIFIERS2_H_ */

