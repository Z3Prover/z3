/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_factory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-28.

Revision History:

--*/
#ifndef ARRAY_FACTORY_H_
#define ARRAY_FACTORY_H_

#include "smt/proto_model/struct_factory.h"

class func_interp;

func_decl * mk_aux_decl_for_array_sort(ast_manager & m, sort * s);

class array_factory : public struct_factory {
    expr * mk_array_interp(sort * s, func_interp * & fi);
    void get_some_args_for(sort * s, ptr_buffer<expr> & args);
    bool mk_two_diff_values_for(sort * s);
public:
    array_factory(ast_manager & m, proto_model & md);

    ~array_factory() override {}

    expr * get_some_value(sort * s) override;

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override;

    expr * get_fresh_value(sort * s) override;
};

#endif /* ARRAY_FACTORY_H_ */

