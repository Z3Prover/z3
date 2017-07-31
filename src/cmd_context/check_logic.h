/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    check_logic.h

Abstract:

    Check whether a given assertion is in the correct logic or not

Author:

    Leonardo de Moura (leonardo) 2011-08-11.

Revision History:

--*/
#ifndef CHECK_LOGIC_H_
#define CHECK_LOGIC_H_

#include "ast/ast.h"

class check_logic {
    struct imp;
    imp * m_imp;
public:
    check_logic();
    ~check_logic();
    void reset();
    void set_logic(ast_manager & m, symbol const & logic);
    bool operator()(expr * n);
    bool operator()(func_decl * f);
    char const * get_last_error() const;
};

#endif
