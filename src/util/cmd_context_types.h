/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_context_types.h

Abstract:

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#pragma once

#include "util/symbol.h"
#include "util/z3_exception.h"
#include<sstream>
class rational;
class expr;
class sort;
class func_decl;
class sexpr;
class cmd_context;

enum cmd_arg_kind {
    CPK_UINT, CPK_BOOL, CPK_DOUBLE, CPK_NUMERAL, 
    CPK_DECIMAL, CPK_STRING, CPK_OPTION_VALUE, 
    CPK_KEYWORD,
    CPK_SYMBOL, CPK_SYMBOL_LIST,
    CPK_SORT,   CPK_SORT_LIST,
    CPK_EXPR,   CPK_EXPR_LIST,
    CPK_FUNC_DECL, CPK_FUNC_DECL_LIST,
    CPK_SORTED_VAR, CPK_SORTED_VAR_LIST,
    CPK_SEXPR,
    CPK_INVALID
};

std::ostream & operator<<(std::ostream & out, cmd_arg_kind k);

typedef cmd_arg_kind param_kind;

class cmd_exception : public default_exception { 
    int         m_line;
    int         m_pos;

    std::string compose(char const* msg, symbol const& s) {
        std::stringstream stm;        
        stm << msg << s;
        return stm.str();
    }
public:
    cmd_exception(char const * msg):default_exception(msg), m_line(-1), m_pos(-1) {}
    cmd_exception(std::string && msg):default_exception(std::move(msg)), m_line(-1), m_pos(-1) {}
    cmd_exception(std::string && msg, int line, int pos):default_exception(std::move(msg)), m_line(line), m_pos(pos) {}
    cmd_exception(char const * msg, symbol const & s): 
        default_exception(compose(msg,s)),m_line(-1),m_pos(-1) {}
    cmd_exception(char const * msg, symbol const & s, int line, int pos): 
        default_exception(compose(msg,s)),m_line(line),m_pos(pos) {}

    bool has_pos() const { return m_line >= 0; }
    int line() const { SASSERT(has_pos()); return m_line; }
    int pos() const { SASSERT(has_pos()); return m_pos; }
};

class stop_parser_exception {
};

typedef std::pair<symbol, sort*> sorted_var;

// A command may have a variable number of arguments.
#define VAR_ARITY UINT_MAX

/**
   \brief Command abstract class.

   Commands may have variable number of argumets.
*/
class cmd {
    symbol m_name;
protected:
    int    m_line;
    int    m_pos;
public:
    cmd(char const * n):m_name(n), m_line(0), m_pos(0) {}
    virtual ~cmd() {}
    virtual void reset(cmd_context & ctx) {}
    virtual void finalize(cmd_context & ctx) {}
    virtual symbol get_name() const { return m_name; }
    virtual char const * get_usage() const { return nullptr; }
    virtual char const * get_descr(cmd_context & ctx) const { return nullptr; }
    virtual unsigned get_arity() const { return 0; }

    // command invocation
    void set_line_pos(int line, int pos) { m_line = line; m_pos = pos; }
    virtual void prepare(cmd_context & ctx) {}
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { UNREACHABLE(); return cmd_arg_kind::CPK_UINT; }
    virtual void set_next_arg(cmd_context & ctx, unsigned val) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, bool val) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, rational const & val) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, double val) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, char const * val) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, symbol const * slist) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, sort * s) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, sort * const * slist) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, expr * t) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, expr * const * tlist) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, sorted_var const & sv) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, sorted_var const * svlist) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, func_decl * f) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, unsigned num, func_decl * const * flist) { UNREACHABLE(); }
    virtual void set_next_arg(cmd_context & ctx, sexpr * n) { UNREACHABLE(); }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {}
};


