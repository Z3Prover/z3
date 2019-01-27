/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_factory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-06.

Revision History:

--*/
#ifndef DATATYPE_FACTORY_H_
#define DATATYPE_FACTORY_H_

#include "smt/proto_model/struct_factory.h"
#include "ast/datatype_decl_plugin.h"

class datatype_factory : public struct_factory {
    datatype_util         m_util;
    obj_map<sort, expr *> m_last_fresh_value;
    
    expr * get_last_fresh_value(sort * s);
    expr * get_almost_fresh_value(sort * s);

    bool is_subterm_of_last_value(app* e);

public:
    datatype_factory(ast_manager & m, proto_model & md);
    ~datatype_factory() override {}
    expr * get_some_value(sort * s) override;
    expr * get_fresh_value(sort * s) override;
};

#endif /* DATATYPE_FACTORY_H_ */

