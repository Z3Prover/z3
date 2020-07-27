/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_model_convert.h

Abstract:

    Model converter for bit-blasting tactics.

Author:

    Leonardo (leonardo) 2011-05-09

Notes:

--*/
#pragma once

#include "tactic/model_converter.h"

model_converter * mk_bit_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits, ptr_vector<func_decl> const& newbits);
model_converter * mk_bv1_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits, ptr_vector<func_decl> const& newbits);

