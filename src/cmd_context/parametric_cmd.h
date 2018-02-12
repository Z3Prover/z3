/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    parametric_cmd.h

Abstract:
    A generic parametric cmd.

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#ifndef PARAMETRIC_CMD_H_
#define PARAMETRIC_CMD_H_

#include "util/params.h"
#include "util/symbol.h"
#include "util/string_buffer.h"
#include "util/cmd_context_types.h"

class parametric_cmd : public cmd {
public:
    symbol                   m_last; 
    string_buffer<> *        m_descr;
    params_ref               m_params;
    scoped_ptr<param_descrs> m_pdescrs;
public:
    parametric_cmd(char const * name):cmd(name), m_descr(nullptr) {}
    ~parametric_cmd() override { if (m_descr) dealloc(m_descr); }
    virtual void init_pdescrs(cmd_context & ctx, param_descrs & d) = 0;
    param_descrs const & pdescrs(cmd_context & ctx) const;
    params_ref const & ps() const { return m_params; }
    virtual char const * get_main_descr() const = 0;
    char const * get_descr(cmd_context & ctx) const override;
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override { m_last = symbol::null; m_params.reset(); }
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override;
    void set_next_arg(cmd_context & ctx, symbol const & s) override;
    void set_next_arg(cmd_context & ctx, unsigned val) override {
        m_params.set_uint(m_last, val); 
        m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, bool val) override {
        m_params.set_bool(m_last, val); 
        m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, rational const & val) override {
        m_params.set_rat(m_last, val); 
        m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, char const * val) override {
        m_params.set_str(m_last, val); 
        m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, sort * s) override {
        NOT_IMPLEMENTED_YET();
        // m_params.set_sort(m_last, s); 
        // m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, expr * t) override {
        NOT_IMPLEMENTED_YET();
        // m_params.set_expr(m_last, t); 
        // m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, func_decl * f) override {
        NOT_IMPLEMENTED_YET();
        // m_params.set_func_decl(m_last, f); 
        // m_last = symbol::null; 
    }
    void set_next_arg(cmd_context & ctx, sexpr * n) override { UNREACHABLE(); }
};

#endif


