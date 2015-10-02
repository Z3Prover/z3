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
#ifndef WELL_SORTED_H_
#define WELL_SORTED_H_

class ast_manager;
class expr;

bool is_well_sorted(ast_manager const & m, expr * n);

#endif /* WELL_SORTED_H_ */

