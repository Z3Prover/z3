/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    parser_params.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2008-04-21.

Revision History:

--*/
#ifndef _PARSER_PARAMS_H_
#define _PARSER_PARAMS_H_

#include"ini_file.h"

struct parser_params {
    bool        m_dump_goal_as_smt; // re-print goal as SMT benchmark.
    bool        m_display_error_for_vs; // print error in vs format.

    parser_params();
    void register_params(ini_params & p);
};

#endif /* _PARSER_PARAMS_H_ */

