/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    dependency_converter.h

Abstract:

    Utility for converting dependencies across subgoals.

Author:

    Nikolaj Bjorner (nbjorner) 2017-11-19

Notes:


--*/
#ifndef DEPENDENCY_CONVERTER_H_
#define DEPENDENCY_CONVERTER_H_

#include "util/ref.h"
#include "ast/ast_pp_util.h"
#include "model/model.h"
#include "tactic/converter.h"

class goal;

class dependency_converter : public converter {
public:
    static dependency_converter* unit(expr_dependency_ref& d);

    static dependency_converter* concat(dependency_converter * dc1, dependency_converter * dc2);

    static dependency_converter* concat(unsigned n, goal * const* goals);

    virtual expr_dependency_ref operator()() = 0;
    
    virtual dependency_converter * translate(ast_translation & translator) = 0;    
};

typedef ref<dependency_converter> dependency_converter_ref;
typedef sref_vector<dependency_converter> dependency_converter_ref_vector;
typedef sref_buffer<dependency_converter> dependency_converter_ref_buffer;

#endif
