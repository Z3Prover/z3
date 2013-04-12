/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_similarity_compressor.h

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-10-22.

Revision History:

--*/
#ifndef _DL_MK_SIMILARITY_COMPRESSOR_H_
#define _DL_MK_SIMILARITY_COMPRESSOR_H_

#include<utility>

#include"map.h"
#include"obj_pair_hashtable.h"

#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Functor for merging groups of similar rules.

       A rule sequence
       
       P("1",x):-Q(x).
       ...
       P("N",x):-Q(x).

       will be replaced by
       
       P(y,x):-Q(x), Aux(y).
       
       and a set of facts

       Aux("1").
       ...
       Aux("N").

       Similar transformation is performed when the varying constant appears in the positive tail.
    */
    class mk_similarity_compressor : public rule_transformer::plugin {

        context &			m_context;
        ast_manager &       m_manager;
        /** number of similar rules necessary for a group to be introduced */
        unsigned            m_threshold_count;
        rule_vector         m_rules;
        rule_ref_vector     m_result_rules;
        bool                m_modified;
        ast_ref_vector      m_pinned;
        
        void merge_class(rule_vector::iterator first, rule_vector::iterator after_last);
        void process_class(rule_set const& source, rule_vector::iterator first, rule_vector::iterator after_last);

        void reset();
    public:
        mk_similarity_compressor(context & ctx);
        
        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_SIMILARITY_COMPRESSOR_H_ */

