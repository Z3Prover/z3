/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2_extra_cmds.cpp

Abstract:

    Additional SMT-specific commands.

Author:

    Christoph (cwinter) 2017-01-16

Notes:

--*/
#include"cmd_context.h"
#include"smt2parser.h"
#include"smt2_extra_cmds.h"

class include_cmd : public cmd {
    char const * m_filename;
public:
    include_cmd() : cmd("include"), m_filename(0) {}
    virtual char const * get_usage() const { return "<string>"; }
    virtual char const * get_descr(cmd_context & ctx) const { return "include a file"; }
    virtual unsigned get_arity() const { return 1; }
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const { return CPK_STRING; }
    virtual void set_next_arg(cmd_context & ctx, char const * val) { m_filename = val; }
    virtual void failure_cleanup(cmd_context & ctx) {}
    virtual void execute(cmd_context & ctx) {
        std::ifstream is(m_filename);
        if (is.bad() || is.fail())
            throw cmd_exception(std::string("failed to open file '") + m_filename + "'");
        parse_smt2_commands(ctx, is, false, params_ref(), m_filename);
        is.close();
    }
    virtual void prepare(cmd_context & ctx) { reset(ctx); }
    virtual void reset(cmd_context & ctx) { m_filename = 0; }
    virtual void finalize(cmd_context & ctx) { reset(ctx); }
};

void install_smt2_extra_cmds(cmd_context & ctx) {
    ctx.insert(alloc(include_cmd));
}
