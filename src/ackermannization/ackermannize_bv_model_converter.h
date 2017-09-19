 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_bv_model_converter.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef ACKERMANNIZE_BV_MODEL_CONVERTER_H_
#define ACKERMANNIZE_BV_MODEL_CONVERTER_H_

#include "tactic/model_converter.h"
#include "ackermannization/ackr_info.h"

model_converter * mk_ackermannize_bv_model_converter(ast_manager & m, const ackr_info_ref& info);

#endif /* ACKERMANNIZE_BV_MODEL_CONVERTER_H_ */
