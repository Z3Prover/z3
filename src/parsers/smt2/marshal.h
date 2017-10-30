/*++
Copyright (c) 2017 Arie Gurfinkel
Module Name:

   marshal.h

Abstract:

   marshaling and unmarshaling of expressions

   --*/
#ifndef _SPACER_MARSHAL_H_
#define _SPACER_MARSHAL_H_

#include <string>
#include <iostream>

#include "ast/ast.h"

std::ostream &marshal(std::ostream &os, expr_ref e, ast_manager &m);
std::string marshal(expr_ref e, ast_manager &m);
expr_ref unmarshal(std::string s, ast_manager &m);
expr_ref unmarshal(std::istream &is, ast_manager &m);



#endif
