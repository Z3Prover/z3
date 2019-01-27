/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_unfold.h

Abstract:

    Unfold rules once, return the unfolded set of rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-15

Revision History:

--*/
#ifndef DL_MK_UNFOLD_H_
#define DL_MK_UNFOLD_H_

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_set.h"
#include "util/uint_set.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/transforms/dl_mk_rule_inliner.h"

namespace datalog {

    /**
       \brief Implements an unfolding transformation.
    */
    class mk_unfold : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        rule_unifier    m_unify;

        void expand_tail(rule& r, unsigned tail_idx, rule_set const& src, rule_set& dst);

    public:
        /**
           \brief Create unfold rule transformer.
         */
        mk_unfold(context & ctx);
        
        rule_set * operator()(rule_set const & source) override;
    };

};

#endif /* DL_MK_UNFOLD_H_ */

