/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_arith_plugin.h

Abstract:

    plugin structure for arithmetic
Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

--*/

#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/euf/euf_plugin.h"
#include "ast/euf/euf_ac_plugin.h"

namespace euf {

    class egraph;

    class arith_plugin : public plugin {
        enum undo_t { undo_add, undo_mul };
        arith_util a;
        svector<undo_t> m_undo;
        ac_plugin m_add, m_mul;
        
    public:
        arith_plugin(egraph& g);

        theory_id get_id() const override { return a.get_family_id(); }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode* eq) override {}

        void undo() override;

        void propagate() override;
        
        std::ostream& display(std::ostream& out) const override;
            
    };
}
