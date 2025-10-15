/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_value_factory.h

Abstract:

    Factory for creating finite set values

--*/
#pragma once

#include "model/struct_factory.h"

/**
   \brief Factory for finite set values.
*/
class finite_set_value_factory : public struct_factory {
public:
    finite_set_value_factory(ast_manager & m, family_id fid, model_core & md);
    
    expr * get_some_value(sort * s) override;
    
    expr * get_fresh_value(sort * s) override;
};

