/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_dag_pp.h

Abstract:

    AST low level pretty printer.

Author:

    Leonardo de Moura (leonardo) 2006-10-19.

Revision History:

--*/
#ifndef _AST_DAG_PP_H_
#define _AST_DAG_PP_H_

#include<iostream>

class ast;

void ast_dag_pp(std::ostream & out, ast_manager& mgr, ast * n);

void ast_dag_pp(std::ostream & out, ast_manager& mgr, ast_mark& mark, ast * n);

#endif /* _AST_DAG_PP_H_ */

