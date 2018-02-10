/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_backwards.h

Abstract:

    Create Horn clauses for backwards flow.

Author:

    Nikolaj Bjorner (nbjorner) 2013-04-17

Revision History:

--*/
#ifndef DL_MK_BACKWARDS_H_
#define DL_MK_BACKWARDS_H_

#include "muz/base/dl_rule_transformer.h"

namespace datalog {

    class mk_backwards : public rule_transformer::plugin {
        ast_manager& m;
        context&     m_ctx;
    public:
        mk_backwards(context & ctx, unsigned priority = 33000);
        ~mk_backwards() override;
        rule_set * operator()(rule_set const & source) override;
    };

};

#endif /* DL_MK_BACKWARDS_H_ */

