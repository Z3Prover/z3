 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr_model_converter_lazy.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#pragma once

#include "tactic/model_converter.h"
#include "ackermannization/ackr_info.h"

model_converter * mk_lackr_model_converter_lazy(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model);

