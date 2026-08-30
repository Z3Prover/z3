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
#pragma once

#include "model/struct_factory.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/term_enumeration.h"

class datatype_factory : public struct_factory {
    datatype_util         m_util;

    // One term_enumeration instance per (top-level) datatype sort. Each
    // instance is seeded with the constructors of the sort and of every
    // datatype sort transitively reachable through constructor argument
    // sorts, and is given an external enumerator that defers to the model
    // for values of non-datatype argument sorts. Used by get_fresh_value to
    // manufacture successive, structurally distinct values of a recursive
    // datatype sort.
    obj_map<sort, term_enumeration *>          m_fresh_enum;
    obj_map<sort, term_enumeration::iterator *> m_fresh_iter;

    term_enumeration & get_enumerator(sort * s, obj_map<sort, term_enumeration *> & cache);

public:
    datatype_factory(ast_manager & m, model_core & md);
    ~datatype_factory() override;
    expr * get_some_value(sort * s) override;
    expr * get_fresh_value(sort * s) override;
};


