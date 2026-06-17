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

#define ATOMIC_CMD(CLS_NAME, NAME, DESCR, ACTION)               \
class CLS_NAME : public cmd {                                   \
public:                                                         \
    CLS_NAME():cmd(NAME) {}                                     \
    char const * get_usage() const override { return 0; }       \
    char const * get_descr(cmd_context & ctx) const override {  \
      return DESCR;                                             \
    }                                                           \
    unsigned get_arity() const override { return 0; }           \
    void execute(cmd_context & ctx) override { ACTION }         \
}

#define UNARY_CMD(CLS_NAME, NAME, USAGE, DESCR, ARG_KIND, ARG_TYPE, ACTION)     \
class CLS_NAME : public cmd {                                                   \
public:                                                                         \
    CLS_NAME():cmd(NAME) {}                                                     \
    char const * get_usage() const override { return USAGE; }                   \
    char const * get_descr(cmd_context & ctx) const override {                  \
      return DESCR;                                                             \
    }                                                                           \
    unsigned get_arity() const override { return 1; }                           \
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {              \
      return ARG_KIND;                                                          \
    }                                                                           \
    void set_next_arg(cmd_context & ctx, ARG_TYPE arg) override { ACTION }      \
}

// Macro for creating commands where the first argument is a symbol
// The second argument cannot be a symbol
#define BINARY_SYM_CMD(CLS_NAME, NAME, USAGE, DESCR, ARG_KIND, ARG_TYPE, ACTION)        \
class CLS_NAME : public cmd {                                                           \
     symbol m_sym;                                                                      \
public:                                                                                 \
    CLS_NAME():cmd(NAME) {}                                                             \
    char const * get_usage() const override { return USAGE; }                           \
    char const * get_descr(cmd_context & ctx) const override { return DESCR; }          \
    unsigned get_arity() const override { return 2; }                                   \
    void prepare(cmd_context & ctx) override { m_sym = symbol::null; }                  \
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override {                      \
      return m_sym == symbol::null ? CPK_SYMBOL : ARG_KIND;                             \
    }                                                                                   \
    void set_next_arg(cmd_context & ctx, symbol const & s) override { m_sym = s; }      \
    void set_next_arg(cmd_context & ctx, ARG_TYPE arg) override { ACTION }              \
}    


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

