/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    echo_tactic.h

Abstract:

    Tactic and probe for dumping data.

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#include <sstream>
#include "tactic/tactic.h"
#include "tactic/probe.h"
#include "cmd_context/cmd_context.h"

class echo_tactic : public skip_tactic {
    cmd_context & m_ctx;
    char const *  m_msg;
    bool          m_newline;
public:
    echo_tactic(cmd_context & ctx, char const * msg, bool newline):m_ctx(ctx), m_msg(msg), m_newline(newline) {}

    char const* name() const override { return "echo"; }

    // (echo "a" "b") builds a sequence of echo tactics; only the last prints a newline.
    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        ctx.leaf("(echo " + tactic_display_string(m_msg) + ")",
                 m_newline ? std::string() : std::string("not parseable: echo without newline"));
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        m_ctx.regular_stream() << m_msg;
        if (m_newline)
            m_ctx.regular_stream() << std::endl;
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_echo_tactic(cmd_context & ctx, char const * msg, bool newline) {
    return alloc(echo_tactic, ctx, msg, newline);
}

class probe_value_tactic : public skip_tactic {
    cmd_context & m_ctx;
    char const *  m_msg;
    probe *       m_p;
    bool          m_newline;
public:
    probe_value_tactic(cmd_context & ctx, char const * msg, probe * p, bool newline):m_ctx(ctx), m_msg(msg), m_p(p), m_newline(newline) {
        SASSERT(m_p);
        m_p->inc_ref(); 
    }

    char const* name() const override { return "probe-value"; }

    void display_pipeline(params_ref const & p, tactic_display_ctx & ctx) override {
        std::ostringstream out;
        m_p->display_sexpr(out << "(echo ");
        out << ")";
        std::string comment;
        if (m_msg || !m_newline)
            comment = "not parseable: probe-value with a message or without newline";
        ctx.leaf(out.str(), comment);
    }
    
    ~probe_value_tactic() override {
        m_p->dec_ref();
    }
    
    void operator()(goal_ref const & in, 
                    goal_ref_buffer & result) override {
        double val = (*m_p)(*(in.get())).get_value();
        if (m_msg)
            m_ctx.diagnostic_stream() << m_msg << " ";
        m_ctx.diagnostic_stream() << val;
        if (m_newline)
            m_ctx.diagnostic_stream() << std::endl;
        skip_tactic::operator()(in, result);
    }
};

tactic * mk_probe_value_tactic(cmd_context & ctx, char const * msg, probe * p, bool newline) {
    return alloc(probe_value_tactic, ctx, msg, p, newline);
}
