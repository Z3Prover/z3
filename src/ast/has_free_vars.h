/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    has_free_vars.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-23.

Revision History:

--*/
#pragma once

class expr;

class contains_vars {
    class imp;
    imp* m_imp;
public:
    contains_vars();
    ~contains_vars();
    bool operator()(expr* n);
};

bool has_free_vars(expr * n);


