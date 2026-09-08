/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    euf_seq_plugin.h

Abstract:

    EUF plugin for associative sequence concatenation.

--*/

#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/euf/euf_assoc_plugin.h"

namespace euf {

    class seq_plugin : public plugin {
        seq_util m_seq;
        assoc_plugin m_concat;

        bool is_concat(enode const* n) const;
        bool is_variable(enode const* n) const;
        bool is_unit(enode const* n) const;

    public:
        seq_plugin(egraph& g);

        theory_id get_id() const override { return m_seq.get_family_id(); }

        void register_node(enode* n) override;
        void merge_eh(enode* n1, enode* n2) override;
        void undo() override;
        void push_scope_eh() override { m_concat.push_scope_eh(); }
        void propagate() override { m_concat.propagate(); }
        std::ostream& display(std::ostream& out) const override { return m_concat.display(out); }
        void collect_statistics(statistics& st) const override { m_concat.collect_statistics(st); }
    };
}
