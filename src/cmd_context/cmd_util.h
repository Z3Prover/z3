/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_util.h

Abstract:
    Macros for defining new SMT2 front-end cmds.

Author:

    Leonardo (leonardo) 2011-04-01

Notes:

--*/
#pragma once

#define ATOMIC_CMD(CLS_NAME, NAME, DESCR, ACTION)                               \
class CLS_NAME : public cmd {                                                   \
public:                                                                         \
    CLS_NAME():cmd(NAME) {}                                                     \
    virtual char const * get_usage() const { return 0; }                        \
    virtual char const * get_descr(cmd_context & ctx) const { return DESCR; }   \
    virtual unsigned get_arity() const { return 0; }                            \
    virtual void execute(cmd_context & ctx) { ACTION }                          \
};

#define UNARY_CMD(CLS_NAME, NAME, USAGE, DESCR, ARG_KIND, ARG_TYPE, ACTION)             \
class CLS_NAME : public cmd {                                                           \
public:                                                                                 \
    CLS_NAME():cmd(NAME) {}                                                             \
    virtual char const * get_usage() const { return USAGE; }                            \
    virtual char const * get_descr(cmd_context & ctx) const { return DESCR; }           \
    virtual unsigned get_arity() const { return 1; }                                    \
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return ARG_KIND; }    \
    virtual void set_next_arg(cmd_context & ctx, ARG_TYPE arg) { ACTION }               \
}

// Macro for creating commands where the first argument is a symbol
// The second argument cannot be a symbol
#define BINARY_SYM_CMD(CLS_NAME, NAME, USAGE, DESCR, ARG_KIND, ARG_TYPE, ACTION)        \
class CLS_NAME : public cmd {                                                           \
    symbol m_sym;                                                                       \
public:                                                                                 \
    CLS_NAME():cmd(NAME) {}                                                             \
    virtual char const * get_usage() const { return USAGE; }                            \
    virtual char const * get_descr(cmd_context & ctx) const { return DESCR; }           \
    virtual unsigned get_arity() const { return 2; }                                    \
    virtual void prepare(cmd_context & ctx) { m_sym = symbol::null; }                   \
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {                       \
        return m_sym == symbol::null ? CPK_SYMBOL : ARG_KIND;                           \
    }                                                                                   \
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { m_sym = s; }       \
    virtual void set_next_arg(cmd_context & ctx, ARG_TYPE arg) { ACTION }               \
};    
   

class ast;
class expr;
class symbol;
class cmd_context;

/**
   \brief Return the AST that is referenced by the global variable v in the given command context.
*/
ast * get_ast_ref(cmd_context & ctx, symbol const & v);
/**
   \brief Return the expression that is referenced by the global variable v in the given command context.
*/
expr * get_expr_ref(cmd_context & ctx, symbol const & v);

/**
   \brief Store t in the global variable v.
*/
void store_expr_ref(cmd_context & ctx, symbol const & v, expr * t);

