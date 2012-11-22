/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_extract_quantifiers.h

Abstract:

    Remove universal quantifiers over interpreted predicates in the body.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-21

Revision History:

--*/
#ifndef _DL_MK_EXTRACT_QUANTIFIERS_H_
#define _DL_MK_EXTRACT_QUANTIFIERS_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Extract universal quantifiers from rules.
    */
    class mk_extract_quantifiers : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        ptr_vector<quantifier_ref_vector> m_refs;
        obj_map<rule const, quantifier_ref_vector*> m_quantifiers;

        void extract(rule& r, rule_set& new_rules);

    public:
        /**
           \brief Create rule transformer that extracts universal quantifiers (over recursive predicates).
         */
        mk_extract_quantifiers(context & ctx);

        virtual ~mk_extract_quantifiers();
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc);

        obj_map<rule const, quantifier_ref_vector*>& quantifiers() { return m_quantifiers; }

        bool has_quantifiers() const { return !m_quantifiers.empty(); }

    };

};

#endif /* _DL_MK_EXTRACT_QUANTIFIERS_H_ */

