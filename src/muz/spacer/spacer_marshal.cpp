/*++
Copyright (c) 2017 Arie Gurfinkel
Module Name:

   spacer_marshal.cpp

Abstract:

   marshaling and unmarshaling of expressions

   --*/
#include "muz/spacer/spacer_marshal.h"

#include <sstream>

#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "util/vector.h"
#include "ast/ast_smt_pp.h"
#include "ast/ast_pp.h"

namespace spacer {
std::ostream &marshal(std::ostream &os, expr_ref e, ast_manager &m)
{
    ast_smt_pp pp(m);
    pp.display_smt2(os, e);
    return os;
}

std::string marshal(expr_ref e, ast_manager &m)
{
    std::stringstream ss;
    marshal(ss, e, m);
    return ss.str();
}


expr_ref unmarshal(std::istream &is, ast_manager &m)
{
    cmd_context ctx(false, &m);
    ctx.set_ignore_check(true);
    if (!parse_smt2_commands(ctx, is)) { return expr_ref(0, m); }

    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    if (it == end) { return expr_ref(m.mk_true(), m); }
    unsigned size = static_cast<unsigned>(end - it);
    return expr_ref(m.mk_and(size, it), m);
}

expr_ref unmarshal(std::string s, ast_manager &m)
{
    std::istringstream is(s);
    return unmarshal(is, m);
}
}
