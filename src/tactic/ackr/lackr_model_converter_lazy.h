 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  lackr_model_converter_lazy.h

 Abstract:


 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef LACKR_MODEL_CONVERTER_LAZY_H_
#define LACKR_MODEL_CONVERTER_LAZY_H_

#include"model_converter.h"
#include"ackr_info.h"

model_converter * mk_lackr_model_converter_lazy(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model);

#endif /* LACKR_MODEL_CONVERTER_LAZY_H_ */
