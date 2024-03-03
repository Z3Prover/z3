/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_arith_plugin.cpp

Abstract:

    plugin structure for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

--*/

#include "ast/euf/euf_arith_plugin.h"
#include "ast/euf/euf_egraph.h"
#include <algorithm>

namespace euf {

    arith_plugin::arith_plugin(egraph& g) :
        plugin(g),
        a(g.get_manager()),
        m_add(g, get_id(), OP_ADD),
        m_mul(g, get_id(), OP_MUL) {
        std::function<void(void)> uadd = [&]() { m_undo.push_back(undo_t::undo_add); };
        m_add.set_undo(uadd);
        std::function<void(void)> umul = [&]() { m_undo.push_back(undo_t::undo_mul); };
        m_mul.set_undo(umul);
    }    

    void arith_plugin::register_node(enode* n) {
        // no-op
    }

    void arith_plugin::merge_eh(enode* n1, enode* n2) {
        m_add.merge_eh(n1, n2);
        m_mul.merge_eh(n1, n2);
    }

    void arith_plugin::propagate() {
        m_add.propagate();
        m_mul.propagate();
    }

    void arith_plugin::undo() {
        auto k = m_undo.back();
        m_undo.pop_back();
        switch (k) {
        case undo_t::undo_add:
            m_add.undo();
            break;
        case undo_t::undo_mul:
            m_mul.undo();
            break;
        default:
            UNREACHABLE();
        }
    }
        
    std::ostream& arith_plugin::display(std::ostream& out) const {
        out << "add\n";
        m_add.display(out);
        out << "mul\n";
        m_mul.display(out);
        return out;
    }
}
