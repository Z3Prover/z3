/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ast_lt.cpp

Abstract:

    Total order on ASTs that does not depend on the internal ids.

Author:

    Leonardo de Moura (leonardo) 2011-04-08

Revision History:

--*/
#include "ast/ast.h"

#define check_symbol(S1,S2) if (S1 != S2) return lt(S1,S2)
#define check_value(V1,V2) if (V1 != V2) return V1 < V2
#define check_bool(B1,B2) if (B1 != B2) return !B1 && B2
#define check_ptr(P1,P2) if (!P1 && P2) return true; if (P1 && !P2) return false
#define check_ast(T1,T2) if (T1 != T2) { n1 = T1; n2 = T2; goto start; }

#define check_parameter(p1, p2) {                               \
    check_value(p1.get_kind(), p2.get_kind());                  \
    switch (p1.get_kind()) {                                    \
    case parameter::PARAM_INT:                                  \
        check_value(p1.get_int(), p2.get_int());                \
        break;                                                  \
    case parameter::PARAM_AST:                                  \
        check_ast(p1.get_ast(), p2.get_ast());                  \
        break;                                                  \
    case parameter::PARAM_SYMBOL:                               \
        check_symbol(p1.get_symbol(), p2.get_symbol());         \
        break;                                                  \
    case parameter::PARAM_RATIONAL:                             \
        check_value(p1.get_rational(), p2.get_rational());      \
        break;                                                  \
    case parameter::PARAM_DOUBLE:                               \
        check_value(p1.get_double(), p2.get_double());          \
        break;                                                  \
    case parameter::PARAM_EXTERNAL:                             \
        check_value(p1.get_ext_id(), p2.get_ext_id());          \
        break;                                                  \
    default:                                                    \
        UNREACHABLE();                                          \
        break;                                                  \
    }                                                           \
}

bool lt(ast * n1, ast * n2) {
    unsigned num;
 start:
    if (n1 == n2)
        return false;
    check_value(n1->get_kind(), n2->get_kind());
    switch(n1->get_kind()) {
    case AST_SORT: 
        check_symbol(to_sort(n1)->get_name(), to_sort(n2)->get_name());
        check_value(to_sort(n1)->get_num_parameters(), to_sort(n2)->get_num_parameters());
        num = to_sort(n1)->get_num_parameters();
        SASSERT(num > 0);
        for (unsigned i = 0; i < num; i++) {
            parameter p1 = to_sort(n1)->get_parameter(i);
            parameter p2 = to_sort(n2)->get_parameter(i);
            check_parameter(p1, p2);
        }
        UNREACHABLE();
        return false;
    case AST_FUNC_DECL:
        check_symbol(to_func_decl(n1)->get_name(), to_func_decl(n2)->get_name());
        check_value(to_func_decl(n1)->get_arity(), to_func_decl(n2)->get_arity());
        check_value(to_func_decl(n1)->get_num_parameters(), to_func_decl(n2)->get_num_parameters());
        num = to_func_decl(n1)->get_num_parameters();
        for (unsigned i = 0; i < num; i++) {
            parameter p1 = to_func_decl(n1)->get_parameter(i);
            parameter p2 = to_func_decl(n2)->get_parameter(i);
            check_parameter(p1, p2);
        }
        num = to_func_decl(n1)->get_arity();
        for (unsigned i = 0; i < num; i++) {
            ast * d1 = to_func_decl(n1)->get_domain(i);
            ast * d2 = to_func_decl(n2)->get_domain(i);
            check_ast(d1, d2);
        }
        n1 = to_func_decl(n1)->get_range();
        n2 = to_func_decl(n2)->get_range();
        goto start;
    case AST_APP:
        check_value(to_app(n1)->get_num_args(), to_app(n2)->get_num_args());
        check_value(to_app(n1)->get_depth(), to_app(n2)->get_depth());
        check_ast(to_app(n1)->get_decl(), to_app(n2)->get_decl());
        num = to_app(n1)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            expr * arg1 = to_app(n1)->get_arg(i);
            expr * arg2 = to_app(n2)->get_arg(i);
            check_ast(arg1, arg2);
        }
        UNREACHABLE();
        return false;
    case AST_QUANTIFIER:
        check_value(to_quantifier(n1)->get_kind(), to_quantifier(n2)->get_kind());
        check_value(to_quantifier(n1)->get_num_decls(), to_quantifier(n2)->get_num_decls());
        check_value(to_quantifier(n1)->get_num_patterns(), to_quantifier(n2)->get_num_patterns());
        check_value(to_quantifier(n1)->get_num_no_patterns(), to_quantifier(n2)->get_num_no_patterns());
        check_value(to_quantifier(n1)->get_weight(), to_quantifier(n2)->get_weight());
        num = to_quantifier(n1)->get_num_decls();
        for (unsigned i = 0; i < num; i++) {
            check_symbol(to_quantifier(n1)->get_decl_name(i), to_quantifier(n2)->get_decl_name(i));
            check_ast(to_quantifier(n1)->get_decl_sort(i), to_quantifier(n2)->get_decl_sort(i));
        }
        num = to_quantifier(n1)->get_num_patterns();
        for (unsigned i = 0; i < num; i++) {
            check_ast(to_quantifier(n1)->get_pattern(i), to_quantifier(n2)->get_pattern(i));
        }
        num = to_quantifier(n1)->get_num_no_patterns();
        for (unsigned i = 0; i < num; i++) {
            check_ast(to_quantifier(n1)->get_no_pattern(i), to_quantifier(n2)->get_no_pattern(i));
        }
        n1 = to_quantifier(n1)->get_expr();
        n2 = to_quantifier(n2)->get_expr();
        goto start;
    case AST_VAR:
        check_value(to_var(n1)->get_idx(), to_var(n2)->get_idx());
        n1 = to_var(n1)->get_sort();
        n2 = to_var(n2)->get_sort();
        goto start;
    default:
        UNREACHABLE();
        return false;
    }
}

bool is_sorted(unsigned num, expr * const * ns) {
    for (unsigned i = 1; i < num; i++) {
        ast * prev = ns[i-1];
        ast * curr = ns[i];
        if (lt(curr, prev))
            return false;
    }
    return true;
}

bool lex_lt(unsigned num, ast * const * n1, ast * const * n2) {
    for (unsigned i = 0; i < num; i ++) {
        if (n1[i] == n2[i])
            continue;
        return lt(n1[i], n2[i]);
    }
    return false;
}
