/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_seq_plugin.cpp

Abstract:

    EUF plugin for associative sequence concatenation.

--*/

#include "ast/euf/euf_seq_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    seq_plugin::seq_plugin(egraph& g):
        plugin(g),
        m_seq(g.get_manager()),
        m_concat(g, get_id()) {
        m_concat.register_associative([this](enode const* n) { return is_concat(n); });
        m_concat.register_variable([this](enode const* n) { return is_variable(n); });
        m_concat.register_unit([this](enode const* n) { return is_unit(n); });
    }

    bool seq_plugin::is_concat(enode const* n) const {
        return m_seq.str.is_concat(n->get_expr());
    }

    bool seq_plugin::is_unit(enode const* n) const {
        expr* e = n->get_expr();
        zstring value;
        return m_seq.str.is_unit(e) || (m_seq.str.is_string(e, value) && value.length() == 1);
    }

    bool seq_plugin::is_variable(enode const* n) const {
        expr* e = n->get_expr();
        return m_seq.is_seq(e) && !is_concat(n) && !is_unit(n) && !m_seq.str.is_empty(e);
    }

    void seq_plugin::register_node(enode* n) {
        m_concat.register_node(n);
    }

    void seq_plugin::merge_eh(enode* n1, enode* n2) {
        m_concat.merge_eh(n1, n2);
    }

    void seq_plugin::undo() {
        m_concat.undo();
    }
}
