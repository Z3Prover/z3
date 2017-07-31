/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cost_parser.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-14.

Revision History:

--*/
#include "parsers/util/cost_parser.h"

cost_parser::cost_parser(ast_manager & m):
    simple_parser(m),
    m_util(m),
    m_vars(m) {
    family_id fid;
    fid = m.get_basic_family_id();
    add_builtin_op("true",    fid, OP_TRUE);
    add_builtin_op("false",   fid, OP_FALSE);
    add_builtin_op("not",     fid, OP_NOT);
    add_builtin_op("and",     fid, OP_AND);
    add_builtin_op("implies", fid, OP_IMPLIES);
    add_builtin_op("or",      fid, OP_OR);
    add_builtin_op("ite",     fid, OP_ITE);
    add_builtin_op("=",       fid, OP_EQ);
    add_builtin_op("iff",     fid, OP_IFF);
    add_builtin_op("xor",     fid, OP_XOR);

    fid = m_util.get_family_id();
    add_builtin_op("+",  fid, OP_ADD);
    add_builtin_op("*",  fid, OP_MUL);
    add_builtin_op("-",  fid, OP_SUB);
    add_builtin_op("/",  fid, OP_DIV);
    add_builtin_op("<=", fid, OP_LE);
    add_builtin_op(">=", fid, OP_GE);
    add_builtin_op("<",  fid, OP_LT);
    add_builtin_op(">",  fid, OP_GT);
}

expr * cost_parser::parse_int(rational const & r) {
    return m_util.mk_numeral(r, false);
}

expr * cost_parser::parse_float(rational const & r) {
    return m_util.mk_numeral(r, false);
}

unsigned cost_parser::add_var(symbol name) {
    sort * real = m_util.mk_real();
    unsigned r  = m_vars.size();
    var * v     = m_manager.mk_var(r, real);
    simple_parser::add_var(name, v);
    m_vars.push_back(v);
    return r;
}

void cost_parser::reset_vars() { 
    simple_parser::reset_vars(); 
    m_vars.reset(); 
}

