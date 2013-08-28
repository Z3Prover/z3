/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_coi_filter.h

Abstract:

    Rule transformer which removes relations which are out of the cone of 
    influence of output relations

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

--*/

#ifndef _DL_MK_COI_FILTER_H_
#define _DL_MK_COI_FILTER_H_

#include "dl_context.h"
#include "dl_rule_transformer.h"

namespace datalog {

    class mk_coi_filter : public rule_transformer::plugin {

        typedef obj_map<func_decl, func_decl *> decl_map;

        ast_manager & m;
        context & m_context;

        rule_set * bottom_up(rule_set const & source);
        rule_set * top_down(rule_set const & source);

    public:
        mk_coi_filter(context & ctx, unsigned priority=45000)
            : plugin(priority),
            m(ctx.get_manager()),
            m_context(ctx) {}

        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_COI_FILTER_H_ */

