/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  qfufbv_ackr_model_converter.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "tactic/smtlogics/qfufbv_ackr_model_converter.h"
#include "ackermannization/ackr_model_converter.h"

model_converter * mk_qfufbv_ackr_model_converter(ast_manager & m, const ackr_info_ref& info, model_ref& abstr_model) {
   return mk_ackr_model_converter(m, info, abstr_model);
}
