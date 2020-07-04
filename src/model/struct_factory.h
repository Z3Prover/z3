/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    struct_factory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-11-06.

Revision History:

--*/
#pragma once

#include "model/value_factory.h"
#include "util/obj_hashtable.h"

class model_core;

/**
   \brief Abstract factory for structured values such as: arrays and algebraic datatypes.
*/
class struct_factory : public value_factory {
protected:
    typedef obj_hashtable<expr> value_set;
    typedef obj_map<sort, value_set *> sort2value_set;

    model_core &          m_model;
    sort2value_set        m_sort2value_set;
    expr_ref_vector       m_values;
    sort_ref_vector       m_sorts;
    ptr_vector<value_set> m_sets;
    
    value_set * get_value_set(sort * s);

public:
    struct_factory(ast_manager & m, family_id fid, model_core & md);

    ~struct_factory() override;

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override;

    void register_value(expr * array_value) override;
};


