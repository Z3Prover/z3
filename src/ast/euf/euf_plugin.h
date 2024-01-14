/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_plugin.h

Abstract:

    plugin structure for euf

    Plugins allow adding equality saturation for theories.

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-08

--*/

#pragma once

#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_justification.h"

namespace euf {

    
    class plugin {
    protected:
        egraph& g;
        void push_plugin_undo(unsigned th_id);
        void push_merge(enode* a, enode* b, justification j);
        void push_merge(enode* a, enode* b);
        enode* mk(expr* e, unsigned n, enode* const* args);
        region& get_region();
    public:
        plugin(egraph& g):
            g(g)
        {}

        virtual ~plugin() {}

        virtual theory_id get_id() const = 0;

        virtual void register_node(enode* n) = 0;
        
        virtual void merge_eh(enode* n1, enode* n2) = 0;

        virtual void diseq_eh(enode* eq) {};

        virtual void propagate() = 0;

        virtual void undo() = 0;
        
        virtual std::ostream& display(std::ostream& out) const = 0;
            
    };
}
