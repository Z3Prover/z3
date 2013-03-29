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
#include"dl_mk_interp_tail_simplifier.h"
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
        mk_interp_tail_simplifier m_simplifier;

        typedef obj_map<app, var*> defs_t;

        bool blast(rule& r, rule_set& new_rules);

        bool is_store_def(expr* e, expr*& x, expr*& y);

        bool ackermanize(expr_ref& body, expr_ref& head);

    public:
        /**
           \brief Create rule transformer that removes array stores and selects by ackermannization.
        */
        mk_array_blast(context & ctx, unsigned priority);

        virtual ~mk_array_blast();
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc);

    };

};

#endif /* _DL_MK_ARRAY_BLAST_H_ */

