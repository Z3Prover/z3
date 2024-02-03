/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_plugin.cpp

Abstract:

    plugin structure for euf

    Plugins allow adding equality saturation for theories.

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-08

--*/

#include "ast/euf/euf_egraph.h"

namespace euf {
    
    void plugin::push_plugin_undo(unsigned th_id) {
        g.push_plugin_undo(th_id);
    }

    void plugin::push_merge(enode* a, enode* b, justification j) {
        TRACE("euf", tout << "push-merge " << g.bpp(a) << " == " << g.bpp(b) << " " << j << "\n");
        g.push_merge(a, b, j);
    }

    void plugin::push_merge(enode* a, enode* b) {
        TRACE("plugin", tout << g.bpp(a) << " == " << g.bpp(b) << "\n");
        g.push_merge(a, b, justification::axiom(get_id()));
    }

    enode* plugin::mk(expr* e, unsigned n, enode* const* args) {
        enode* r = g.find(e);
        if (!r)
            r = g.mk(e, 0, n, args);
        return r;
    }

    region& plugin::get_region() {
        return g.m_region;
    }
}
