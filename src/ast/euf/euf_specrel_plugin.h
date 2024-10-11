/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_specrel_plugin.h

Abstract:

    plugin structure for specrel functions

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-11

--*/

#pragma once

#include <iostream>
#include "util/scoped_ptr_vector.h"
#include "ast/special_relations_decl_plugin.h"
#include "ast/euf/euf_plugin.h"
#include "ast/euf/euf_ac_plugin.h"

namespace euf {

    class specrel_plugin : public plugin {
        scoped_ptr_vector<ac_plugin> m_plugins;
        ptr_vector<ac_plugin> m_undo;
        obj_map<func_decl, ac_plugin*> m_decl2plugin;
        special_relations_util sp;
        
    public:

        specrel_plugin(egraph& g);
        
        theory_id get_id() const override { return sp.get_family_id(); }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode* eq) override;

        void undo() override;

        void propagate() override;
        
        std::ostream& display(std::ostream& out) const override;

    };

}
