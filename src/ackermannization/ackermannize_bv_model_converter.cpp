/*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackermannize_bv_model_converter.cpp

 Abstract:


 Author:

 Mikolas Janota (MikolasJanota)

 Revision History:
--*/
#include "ackermannization/ackr_model_converter.h"
#include "ackermannization/ackermannize_bv_model_converter.h"

model_converter * mk_ackermannize_bv_model_converter(ast_manager & m, const ackr_info_ref& info) {
    return mk_ackr_model_converter(m, info);
}
