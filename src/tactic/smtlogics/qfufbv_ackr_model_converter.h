 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qfufbv_ackr_model_converter.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#pragma once

#include "tactic/model_converter.h"
#include "ackermannization/ackr_info.h"

model_converter * mk_qfufbv_ackr_model_converter(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model);

