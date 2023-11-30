/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_specrel_plugin.cpp

Abstract:

    plugin structure for specrel

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

--*/

#include "ast/euf/euf_specrel_plugin.h"
#include "ast/euf/euf_egraph.h"
#include <algorithm>

namespace euf {

    specrel_plugin::specrel_plugin(egraph& g) :
        plugin(g),
        sp(g.get_manager()) {
    }    

    void specrel_plugin::register_node(enode* n) {
        func_decl* f = n->get_decl();
        if (!f)
            return;
        if (!sp.is_ac(f))
            return;
        ac_plugin* p = nullptr;
        if (!m_decl2plugin.find(f, p)) {
            p = alloc(ac_plugin, g, f);
            m_decl2plugin.insert(f, p);
            m_plugins.push_back(p);
            std::function<void(void)> undo_op = [&]() { m_undo.push_back(p); };
            p->set_undo(undo_op);
        }
    }

    void specrel_plugin::merge_eh(enode* n1, enode* n2) {
        for (auto * p : m_plugins)
            p->merge_eh(n1, n2);
    }

    void specrel_plugin::diseq_eh(enode* eq) {
        for (auto* p : m_plugins)
            p->diseq_eh(eq);
    }

    void specrel_plugin::propagate() {
        for (auto * p : m_plugins)
            p->propagate();        
    }

    void specrel_plugin::undo() {
        auto p = m_undo.back();
        m_undo.pop_back();
        p->undo();
    }
        
    std::ostream& specrel_plugin::display(std::ostream& out) const {
        for (auto * p : m_plugins)
            p->display(out);
        return out;
    }
}