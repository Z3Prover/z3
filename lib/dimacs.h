/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dimacs.h

Abstract:

    Dimacs CNF parser

Author:

    Leonardo de Moura (leonardo) 2011-07-26.

Revision History:

--*/
#ifndef _DIMACS_H_
#define _DIMACS_H_

#include"sat_types.h"

void parse_dimacs(std::istream & s, sat::solver & solver);

#endif /* _DIMACS_PARSER_H_ */

