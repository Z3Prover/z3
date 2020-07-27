/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    well_sorted.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-29.

Revision History:

--*/
#pragma once

class ast_manager;
class expr;

bool is_well_sorted(ast_manager const & m, expr * n);


