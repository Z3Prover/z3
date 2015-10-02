/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    simple_parser.h

Abstract:

    Simple sexpr parser

Author:

    Leonardo de Moura (leonardo) 2008-03-31.

Revision History:

--*/
#ifndef SIMPLE_PARSER_H_
#define SIMPLE_PARSER_H_

#include"ast.h"
#include"map.h"

class scanner;

/**
   \brief Simple sexpr parser.
   This class is used to parse small expressions used for configuring Z3.
*/
class simple_parser {
protected:
    struct parser_error {};
    struct builtin_op {
        family_id m_family_id;
        decl_kind m_kind;
        builtin_op() : m_family_id(null_family_id), m_kind(0) {}
        builtin_op(family_id fid, decl_kind k) : m_family_id(fid), m_kind(k) {}
    };
    typedef map<symbol, builtin_op, symbol_hash_proc, symbol_eq_proc> op_map;
    typedef map<symbol, var *, symbol_hash_proc, symbol_eq_proc>   var_map;
    ast_manager &    m_manager;
    op_map           m_builtin;
    var_map          m_vars;
    expr_ref_vector  m_exprs;
    expr * parse_expr(scanner & s);
public:
    simple_parser(ast_manager & m);
    virtual ~simple_parser();
    void add_builtin_op(symbol const & s, family_id fid, decl_kind kind);
    void add_builtin_op(char const * str, family_id fid, decl_kind kind);
    void add_var(symbol const & s, var * v);
    void add_var(char const * str, var * v);
    void reset();
    void reset_vars();
    bool parse(std::istream & in, expr_ref & result);
    bool parse_string(char const * str, expr_ref & result);
    bool parse_file(char const * file, expr_ref & result);
    virtual expr * parse_int(rational const & r) { throw parser_error(); }
    virtual expr * parse_float(rational const & r) { throw parser_error(); }
};

#endif /* SIMPLE_PARSER_H_ */

