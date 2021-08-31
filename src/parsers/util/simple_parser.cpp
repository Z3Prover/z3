/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    simple_parser.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-31.

Revision History:

--*/
#include<fstream>
#include<sstream>
#include "parsers/util/simple_parser.h"
#include "util/warning.h"
#include "parsers/util/scanner.h"

simple_parser::simple_parser(ast_manager & m):
    m_manager(m),
    m_exprs(m) {
}

simple_parser::~simple_parser() {
}

void simple_parser::add_builtin_op(symbol const & s, family_id fid, decl_kind kind) {
    SASSERT(!m_builtin.contains(s));
    SASSERT(!m_vars.contains(s));
    m_builtin.insert(s, builtin_op(fid, kind));
}

void simple_parser::add_builtin_op(char const * str, family_id fid, decl_kind kind) {
    add_builtin_op(symbol(str), fid, kind);
}

void simple_parser::add_var(symbol const & s, var * v) {
    SASSERT(!m_builtin.contains(s));
    SASSERT(!m_vars.contains(s));
    m_vars.insert(s, v);
}

void simple_parser::add_var(char const * str, var * v) {
    add_var(symbol(str), v);
}

void simple_parser::reset() {
    m_builtin.reset();
    m_vars.reset();
    m_exprs.reset();
}

void simple_parser::reset_vars() {
    m_vars.reset();
}

expr * simple_parser::parse_expr(scanner & s) {
    builtin_op op; 
    var * v;
    expr * r;
    scanner::token token;
    token = s.scan();
    switch (token) {
    case scanner::LEFT_PAREN:
        token = s.scan();
        if (token != scanner::ID_TOKEN)
            throw parser_error();
        if (m_builtin.find(s.get_id(), op)) {
            ptr_vector<expr> args;
            while (true) {
                expr * arg = parse_expr(s);
                if (arg) {
                    args.push_back(arg);
                }
                else {
                    expr * r = m_manager.mk_app(op.m_family_id, op.m_kind, args.size(), args.data());
                    m_exprs.push_back(r);
                    return r;
                }
            }
        }
        throw parser_error();
    case scanner::RIGHT_PAREN:
        return nullptr;
    case scanner::ID_TOKEN:
        if (m_builtin.find(s.get_id(), op)) {
            expr * r = m_manager.mk_const(op.m_family_id, op.m_kind);
            m_exprs.push_back(r);
            return r;
        }
        else if (m_vars.find(s.get_id(), v)) {
            return v;
        }
        throw parser_error();
    case scanner::INT_TOKEN:
        r = parse_int(s.get_number());
        m_exprs.push_back(r);
        return r;
    case scanner::FLOAT_TOKEN:
        r = parse_float(s.get_number());
        m_exprs.push_back(r);
        return r;
    default:
        throw parser_error();
    }
}

bool simple_parser::parse(std::istream & in, expr_ref & result) {
    scanner s(in, std::cerr, false);
    try {
        result = parse_expr(s);
        if (!result)
            throw parser_error();
    }
    catch (const parser_error &) {
        warning_msg("parser error");
        return false;
    } 
    m_exprs.reset();
    return result.get() != nullptr;
}

bool simple_parser::parse_string(char const * str, expr_ref & result) {
    std::string s = str;
    std::istringstream is(s);
    return parse(is, result);
}
 
bool simple_parser::parse_file(char const * file, expr_ref & result) {
    if (file != nullptr) {
        std::ifstream stream(file);
        if (!stream) {
            warning_msg("ERROR: could not open file '%s'.", file);
            return false;
        }
        return parse(stream, result);
    }
    else {
        return parse(std::cin, result);
    }
}


