/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_bit_blast.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2012-08-30

Revision History:

--*/
#ifndef _DL_MK_BIT_BLAST_H_
#define _DL_MK_BIT_BLAST_H_

#include<utility>

#include"map.h"
#include"obj_pair_hashtable.h"
#include"dl_context.h"
#include"dl_rule_set.h"
#include"dl_rule_transformer.h"

namespace datalog {

    /**
       \brief Functor for bit-blasting a rule set.
    */

    class mk_bit_blast : public rule_transformer::plugin {
        class impl;

        impl*            m_impl;
        void blast(expr_ref& b);
        void reset();

    public:
        mk_bit_blast(context & ctx, unsigned priority = 35000);
        ~mk_bit_blast();
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc);
    };

};

#endif /* _DL_MK_BIT_BLAST_H_ */

