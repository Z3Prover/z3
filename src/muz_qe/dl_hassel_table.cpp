/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_table.cpp

Abstract:

    <abstract>

Revision History:

--*/

#include "ast_printer.h"
#include "dl_context.h"
#include "dl_util.h"
#include "dl_hassel_table.h"


namespace datalog {

    hassel_table_plugin::hassel_table_plugin(relation_manager & manager)
        : common_hassel_table_plugin(symbol("hassel"), manager) {}

}
