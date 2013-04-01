/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_loop_counter.h

Abstract:

    Add loop counter argument to relations.

Author:

    Nikolaj Bjorner (nbjorner) 2013-03-31

Revision History:

--*/
#ifndef _DL_MK_LOOP_COUNTER_H_
#define _DL_MK_LOOP_COUNTER_H_

#include"dl_rule_transformer.h"

namespace datalog {

    class mk_loop_counter : public rule_transformer::plugin {
        app_ref add_arg(ast_manager& m, app* fn, unsigned idx);        
    public:
        mk_loop_counter(context & ctx, unsigned priority = 33000);
        ~mk_loop_counter();
        
        rule_set * operator()(rule_set const & source);
    };

};

#endif /* _DL_MK_LOOP_COUNTER_H_ */

