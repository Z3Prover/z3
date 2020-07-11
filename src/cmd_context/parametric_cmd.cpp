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
#include<sstream>
#include "cmd_context/cmd_context.h"
#include "cmd_context/parametric_cmd.h"

char const * parametric_cmd::get_descr(cmd_context & ctx) const { 
    if (m_descr == nullptr) {
        const_cast<parametric_cmd*>(this)->m_descr = alloc(string_buffer<>);
        m_descr->append(get_main_descr());
        m_descr->append("\nThe following options are available:\n");
        std::ostringstream buf;
        pdescrs(ctx).display(buf, 2);
        m_descr->append(buf.str());
    }
    return m_descr->c_str();
}

cmd_arg_kind parametric_cmd::next_arg_kind(cmd_context & ctx) const {
    if (m_last == symbol::null) return CPK_KEYWORD;
    return pdescrs(ctx).get_kind(m_last);
}

void parametric_cmd::set_next_arg(cmd_context & ctx, symbol const & s) { 
    if (m_last == symbol::null) {
        m_last = symbol(norm_param_name(s));
        if (pdescrs(ctx).get_kind(m_last.bare_str()) == CPK_INVALID)
            throw cmd_exception("invalid keyword argument");
        return;
    }
    else {
        m_params.set_sym(m_last.bare_str(), s);
        m_last = symbol::null;
    }
}

param_descrs const & parametric_cmd::pdescrs(cmd_context & ctx) const {
    if (!m_pdescrs) {
        parametric_cmd * _this = const_cast<parametric_cmd*>(this);
        _this->m_pdescrs = alloc(param_descrs);
        _this->init_pdescrs(ctx, *(_this->m_pdescrs));
    }
    return *m_pdescrs;
}








