/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    euf_bv_plugin.h

Abstract:

    plugin structure for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2023-11-08
    Jakob Rath 2023-11-08


--*/

#pragma once

#include "util/trail.h"
#include "ast/bv_decl_plugin.h"
#include "ast/euf/euf_plugin.h"

namespace euf {

    class egraph;

    class bv_plugin : public plugin {
        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();
        
        struct slice_info {
            unsigned cut = null_cut;  // = bv.get_bv_size(lo)
            enode* hi = nullptr;      //
            enode* lo = nullptr;      //
            enode* value = nullptr;
            void reset() { *this = slice_info(); }
        };
        using slice_info_vector = svector<slice_info>;

        bv_util                 bv;
        slice_info_vector       m_info;         // indexed by enode::get_id()
        enode_vector m_xs, m_ys;

        std::function<void(enode*)> m_ensure_th_var;

        bool is_concat(enode* n) const { return bv.is_concat(n->get_expr()); }
        bool is_concat(enode* n, enode*& a, enode*& b) { return is_concat(n) && n->num_args() == 2 && (a = n->get_arg(0), b = n->get_arg(1), true); }
        bool is_extract(enode* n, unsigned& lo, unsigned& hi) { expr* body;  return bv.is_extract(n->get_expr(), lo, hi, body); }
        bool is_extract(enode* n) const { return bv.is_extract(n->get_expr()); }
        unsigned width(enode* n) const { return bv.get_bv_size(n->get_expr()); }        

        enode* mk_extract(enode* n, unsigned lo, unsigned hi);
        enode* mk_concat(enode* hi, enode* lo);
        enode* mk_value_concat(enode* hi, enode* lo);
        enode* mk_value(rational const& v, unsigned sz);
        unsigned width(enode* n) { return bv.get_bv_size(n->get_expr()); }
        bool  is_value(enode* n) { return n->get_root()->interpreted(); }
        rational get_value(enode* n) { rational val; VERIFY(bv.is_numeral(n->get_interpreted()->get_expr(), val)); return val; }
        slice_info& info(enode* n) { unsigned id = n->get_id(); m_info.reserve(id + 1); return m_info[id]; }
        bool has_sub(enode* n) { return !!info(n).lo; }
        enode* sub_lo(enode* n) { return info(n).lo; }
        enode* sub_hi(enode* n) { return info(n).hi; }

        bool m_internal = false;
        void ensure_slice(enode* n, unsigned lo, unsigned hi);


        void split(enode* n, unsigned cut);

        bool unfold_width(enode* x, enode_vector& xs, enode* y, enode_vector& ys);
        bool unfold_sub(enode* x, enode_vector& xs);
        void merge(enode_vector& xs, enode_vector& ys, justification j);
        svector<std::tuple<unsigned, unsigned, unsigned>> m_ensure_concat;
        void propagate_extract(enode* n);
        void propagate_values(enode* n);

        vector<unsigned_vector> m_offsets;
        svector<std::pair<enode*, unsigned>> m_todo;
        svector<std::tuple<enode*, unsigned, unsigned>> m_jtodo;
        void clear_offsets();


        ptr_vector<trail> m_trail;
        
        class undo_split;
        void push_undo_split(enode* n);

        vector<std::variant<enode*, enode_pair>> m_queue;
        unsigned m_qhead = 0;        
        void propagate_register_node(enode* n);
        void propagate_merge(enode* a, enode* b);
        
    public:
        bv_plugin(egraph& g);

        theory_id get_id() const override { return bv.get_family_id(); }

        void register_node(enode* n) override;

        void merge_eh(enode* n1, enode* n2) override;

        void diseq_eh(enode* eq) override {}

        void propagate() override;

        void undo() override;

        void set_ensure_th_var(std::function<void(enode*)>& f) { m_ensure_th_var = f; }
        
        std::ostream& display(std::ostream& out) const override;

        void sub_slices(enode* n, std::function<bool(enode*, unsigned)>& consumer);

        void super_slices(enode* n, std::function<bool(enode*, unsigned)>& consumer);

        void explain_slice(enode* a, unsigned offset, enode* b, std::function<void(enode*, enode*)>& consumer);
            
    };
}
