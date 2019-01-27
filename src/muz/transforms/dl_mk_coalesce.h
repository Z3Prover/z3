
/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_coalesce.h

Abstract:

    Coalesce rules with shared bodies.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-15

Revision History:

--*/
#ifndef DL_MK_COALESCE_H_
#define DL_MK_COALESCE_H_

#include "muz/base/dl_context.h"
#include "muz/base/dl_rule_set.h"
#include "util/uint_set.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/transforms/dl_mk_rule_inliner.h"

namespace datalog {

    /**
       \brief Implements an unfolding transformation.
    */
    class mk_coalesce : public rule_transformer::plugin {
        context&        m_ctx;
        ast_manager&    m;
        rule_manager&   rm;
        expr_ref_vector m_sub1, m_sub2;
        unsigned        m_idx;

        void mk_pred(app_ref& pred, app* p1, app* p2);

        void extract_conjs(expr_ref_vector const& sub, rule const& rl, expr_ref& result);

        bool same_body(rule const& r1, rule const& r2) const;

        void merge_rules(rule_ref& tgt, rule const& src);

    public:
        /**
           \brief Create coalesced rules.
         */
        mk_coalesce(context & ctx);
        
        rule_set * operator()(rule_set const & source) override;
    };

};

#endif /* DL_MK_COALESCE_H_ */

