/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_array_blast.h

Abstract:

    Remove array variables from rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

Revision History:

--*/
#ifndef _DL_MK_ARRAY_BLAST_H_
#define _DL_MK_ARRAY_BLAST_H_

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"
#include "equiv_proof_converter.h"
#include "array_decl_plugin.h"

namespace datalog {

    /**
       \brief Blast occurrences of arrays in rules
    */
    class mk_array_blast : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        array_util      a;
        rule_manager&   rm;
        params_ref      m_params;
        th_rewriter     m_rewriter;
        equiv_proof_converter* m_pc;

        bool blast(rule& r, rule_set& new_rules);

        bool is_store_def(expr* e, expr*& x, expr*& y);

    public:
        /**
           \brief Create rule transformer that extracts universal quantifiers (over recursive predicates).
        */
        mk_array_blast(context & ctx, unsigned priority);

        virtual ~mk_array_blast();
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc);

    };

};

#endif /* _DL_MK_ARRAY_BLAST_H_ */

