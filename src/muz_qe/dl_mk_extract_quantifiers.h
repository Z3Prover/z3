/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers.h

Abstract:

    Replace universal quantifiers over interpreted predicates in the body
    by instantiations mined using bounded model checking search.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/
#ifndef _DL_MK_EXTRACT_QUANTIFIERS_H_
#define _DL_MK_EXTRACT_QUANTIFIERS_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include"obj_pair_hashtable.h"

namespace datalog {

    /**
       \brief Extract universal quantifiers from rules.
    */
    class mk_extract_quantifiers : public rule_transformer::plugin {

        class collect_insts;

        context&                                    m_ctx;
        ast_manager&                                m;
        rule_manager&                               rm;
        func_decl_ref                               m_query_pred;        
        bool                                        m_has_quantifiers;
        obj_map<rule const, quantifier_ref_vector*> m_quantifiers;

        void reset();

        void extract(rule& r, rule_set& new_rules);

        void rule2formula(
            rule& r,
            obj_map<quantifier, expr_ref_vector*> const& insts,
            expr_ref& fml,
            app_ref_vector& sub);


        void add_binding(
            app_ref_vector const&        var_inst,
            expr_ref_vector&             bindings,
            quantifier*                  q, 
            expr_ref_vector const&       instantiation,
            obj_map<quantifier, expr_ref_vector*>& insts);

        void apply_binding(
            app_ref_vector const&        var_inst,
            expr_ref_vector&             bindings,
            quantifier*                  q, 
            expr_ref_vector const&       instantiation,
            obj_map<quantifier, expr_ref_vector*>& insts);


    public:
        /**
           \brief Create rule transformer that extracts universal quantifiers (over recursive predicates).
         */
        mk_extract_quantifiers(context & ctx);

        virtual ~mk_extract_quantifiers();

        void set_query(func_decl* q);
        
        rule_set * operator()(rule_set const & source);

        bool has_quantifiers() { return m_has_quantifiers; }

        obj_map<rule const, quantifier_ref_vector*>& quantifiers() { return m_quantifiers; }

        void ensure_predicate(expr* e, unsigned& max_var, app_ref_vector& tail);

        bool find_instantiations_proof_based(
            expr*                        fml,
            app_ref_vector const&        var_inst,
            obj_map<quantifier, expr_ref_vector*>& insts,
            expr_ref_vector&             bindings);

    };

};

#endif /* _DL_MK_EXTRACT_QUANTIFIERS_H_ */

