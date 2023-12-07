/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    occurs.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-07.

Revision History:

--*/
#pragma once

#include "util/vector.h"
#include "ast/ast.h"

/**
   \brief Return true if n1 occurs in n2
*/
bool occurs(expr * n1, expr * n2);

/**
   \brief Return true if d is used in n
*/
bool occurs(func_decl * d, expr * n);

/**
* \brief Return true if s1 occurs in s2
*/
bool occurs(sort* s1, sort* s2);

/**
* \brief Mark sub-expressions of to_check by whether v occurs in these.
*/
void mark_occurs(ptr_vector<expr>& to_check, expr* v, expr_mark& occurs);


