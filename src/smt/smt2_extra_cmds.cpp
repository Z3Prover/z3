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
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "smt/smt2_extra_cmds.h"

class include_cmd : public cmd {
    char const * m_filename;
public:
    include_cmd() : cmd("include"), m_filename(nullptr) {}
    char const * get_usage() const override { return "<string>"; }
    char const * get_descr(cmd_context & ctx) const override { return "include a file"; }
    unsigned get_arity() const override { return 1; }
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_STRING; }
    void set_next_arg(cmd_context & ctx, char const * val) override { m_filename = val; }
    void failure_cleanup(cmd_context & ctx) override {}
    void execute(cmd_context & ctx) override {
        std::ifstream is(m_filename);
        if (is.bad() || is.fail())
            throw cmd_exception(std::string("failed to open file '") + m_filename + "'");
        parse_smt2_commands(ctx, is, false, params_ref(), m_filename);
        is.close();
    }
    void prepare(cmd_context & ctx) override { reset(ctx); }
    void reset(cmd_context & ctx) override { m_filename = nullptr; }
    void finalize(cmd_context & ctx) override { reset(ctx); }
};

void install_smt2_extra_cmds(cmd_context & ctx) {
    ctx.insert(alloc(include_cmd));
}
