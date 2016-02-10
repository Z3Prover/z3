 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qfufbv_ackr_model_converter.h

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
 --*/
#ifndef QFUFBV_ACKR_MODEL_CONVERTER_H_
#define QFUFBV_ACKR_MODEL_CONVERTER_H_

#include"model_converter.h"
#include"ackr_info.h"

model_converter * mk_qfufbv_ackr_model_converter(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model);

#endif /* QFUFBV_ACKR_MODEL_CONVERTER_H_ */
