/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    dl_simplifier_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-08-10

Revision History:

--*/
#ifndef _DL_SIMPLIFIER_PLUGIN_H_
#define _DL_SIMPLIFIER_PLUGIN_H_

#include"dl_decl_plugin.h"
#include "simplifier_plugin.h"

namespace datalog {

    class dl_simplifier_plugin : public simplifier_plugin {
        dl_decl_util  m_util;
    public:
        dl_simplifier_plugin(ast_manager& m);
        
        virtual bool reduce(func_decl * f, unsigned num_args, expr* const* args, expr_ref& result);
        
    };
    
};
#endif /* _DL_SIMPLIFIER_PLUGIN_H_ */

