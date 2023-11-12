/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_ac_plugin.h

Abstract:

    plugin structure for ac functions
Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11
    Jakob Rath 2023-11-11


--*/

#pragma once

#include "ast/euf/euf_plugin.h"

namespace euf {

    
    class ac_plugin : public plugin {
        struct eq {
            enode_vector l, r;            
        };
        vector<eq>           m_eqs;
        vector<enode_vector> m_use;
        unsigned             m_fid;
        unsigned             m_op;

        void push_eq(enode* l, enode* r);
    public:

        ac_plugin(egraph& g, unsigned fid, unsigned op);
        
        unsigned get_id() const override { return m_fid; }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2, justification j) override;

        void diseq_eh(enode* n1, enode* n2) override;

        void undo() override;
        
        std::ostream& display(std::ostream& out) const override;
    };
