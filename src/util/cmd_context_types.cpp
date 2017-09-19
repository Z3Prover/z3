/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_context_types.h

Abstract:

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#include<iostream>
#include "util/cmd_context_types.h"

std::ostream & operator<<(std::ostream & out, cmd_arg_kind k) {
    switch (k) {
    case CPK_UINT: out << "unsigned int"; break;
    case CPK_BOOL: out << "bool"; break;
    case CPK_DOUBLE: out << "double"; break;
    case CPK_NUMERAL: out << "rational"; break;
    case CPK_DECIMAL: out << "rational"; break;
    case CPK_STRING:  out << "string"; break;
    case CPK_OPTION_VALUE: out << "optional-value"; break;
    case CPK_KEYWORD: out << "keyword"; break;
    case CPK_SYMBOL: out << "symbol"; break;
    case CPK_SYMBOL_LIST: out << "symbol-list"; break;
    case CPK_SORT: out << "sort"; break;
    case CPK_SORT_LIST: out << "sort-list"; break;
    case CPK_EXPR: out << "expression"; break;
    case CPK_EXPR_LIST: out << "expression-list"; break;
    case CPK_FUNC_DECL: out << "declaration"; break;
    case CPK_FUNC_DECL_LIST: out << "declaration-list"; break;
    case CPK_SORTED_VAR: out << "sorted-variable"; break;
    case CPK_SORTED_VAR_LIST: out << "sorted-variable-list"; break;
    case CPK_SEXPR: out << "s-expression"; break;
    default: out << "unknown"; break;
    }
    return out;
}
