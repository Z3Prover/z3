 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_bv_model_converter.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#pragma once

#include "tactic/model_converter.h"
#include "ackermannization/ackr_info.h"

model_converter * mk_ackermannize_bv_model_converter(ast_manager & m, const ackr_info_ref& info);

