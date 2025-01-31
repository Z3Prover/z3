/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    sls_array_plugin.h

Abstract:

    Theory plugin for arrays local search

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-06

--*/
#pragma once

#include "ast/sls/sls_context.h"
#include "ast/array_decl_plugin.h"
#include "ast/euf/euf_egraph.h"

namespace sls {

    class euf_plugin;

    class array_plugin : public plugin {
        struct select_args {
            euf::enode* sel = nullptr;
            select_args(euf::enode* s) : sel(s) {}
            select_args() {}
        };
        struct select_args_hash {
            unsigned operator()(select_args const& a) const {
                unsigned h = 0;
                for (unsigned i = 1; i < a.sel->num_args(); ++i)
                    h ^= a.sel->get_arg(i)->get_root()->hash();
                return h;
            };
        };
        struct select_args_eq {
            bool operator()(select_args const& a, select_args const& b) const {
                SASSERT(a.sel->num_args() == b.sel->num_args());
                for (unsigned i = 1; i < a.sel->num_args(); ++i)
                    if (a.sel->get_arg(i)->get_root() != b.sel->get_arg(i)->get_root())
                        return false;
                return true;
            }
        };
        typedef map<select_args, euf::enode*, select_args_hash, select_args_eq> select2value;
        typedef obj_map<euf::enode, select2value> kv;
        struct stats {
            unsigned m_num_conflicts = 0;
            unsigned m_num_axioms = 0;
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        euf_plugin&    euf;
        array_util     a;
        scoped_ptr<euf::egraph> m_g;
        scoped_ptr<kv>          m_kv;
        bool  m_add_conflicts = true;
        bool  m_has_arrays = false;
        stats m_stats;

        enum axiom_t { store_axiom1, store_axiom2_down, store_axiom2_up, map_axiom, const_axiom };
        struct axiom_instance {
            axiom_t t;
            euf::enode* sto; euf::enode* sel;
        };
        svector<axiom_instance> m_delayed_axioms;
        unsigned store_axiom1_index(euf::enode* n) { m_delayed_axioms.push_back({ store_axiom1, n, nullptr }); return m_delayed_axioms.size() - 1; }
        unsigned store_axiom2_down_index(euf::enode* sto, euf::enode* sel) { m_delayed_axioms.push_back({ store_axiom2_down, sto, sel }); return m_delayed_axioms.size() - 1; }
        unsigned store_axiom2_up_index(euf::enode* sto, euf::enode* sel) { m_delayed_axioms.push_back({ store_axiom2_up, sto, sel }); return m_delayed_axioms.size() - 1; }
        unsigned map_axiom_index(euf::enode* sto, euf::enode* sel) { m_delayed_axioms.push_back({ map_axiom, sto, sel }); return m_delayed_axioms.size() - 1; }
        unsigned const_axiom_index(euf::enode* val, euf::enode* sel) { m_delayed_axioms.push_back({ const_axiom, val, sel }); return m_delayed_axioms.size() - 1; }

        void add_eq_axiom(euf::enode* x, euf::enode* y) {
            ++m_stats.m_num_axioms;
            expr_ref eq(m.mk_eq(x->get_expr(), y->get_expr()), m);
            ctx.add_theory_axiom(eq);
        }

        void init_egraph(euf::egraph& g);
        void init_kv(euf::egraph& g, kv& kv);
        void saturate(euf::egraph& g);
        bool saturate_extensionality(euf::egraph& g);
        void collect_shared(euf::egraph& g, euf::enode_vector& shared);
        bool is_shared_arg(euf::enode* r);
        void saturate_store(euf::egraph& g, euf::enode* n);
        void saturate_const(euf::egraph& g, euf::enode* n);
        void saturate_map(euf::egraph& g, euf::enode* n);
        void force_store_axiom1(euf::egraph& g, euf::enode* n);
        void force_store_axiom2_down(euf::egraph& g, euf::enode* sto, euf::enode* sel);
        void force_store_axiom2_up(euf::egraph& g, euf::enode* sto, euf::enode* sel);
        void force_const_axiom(euf::egraph& g, euf::enode* cn, euf::enode* sel);
        void add_map_axiom(euf::egraph& g, euf::enode* n, euf::enode* sel);
        void add_store_axiom1(app* sto);
        void add_store_axiom2(app* sto, app* sel);
        bool add_extensionality_axiom(expr* a, expr* b);
        bool are_distinct(euf::enode* a, euf::enode* b);
        bool eq_args(euf::enode* sto, euf::enode* sel);
        euf::enode* mk_select(euf::egraph& g, euf::enode* b, euf::enode* sel);

        void resolve_conflict();
        size_t* to_ptr(sat::literal l) { return reinterpret_cast<size_t*>((size_t)(l.index() << 4)); };
        size_t* to_ptr(euf::enode* t) { return reinterpret_cast<size_t*>((reinterpret_cast<size_t>(t) << 4) + 1); }
        size_t* to_ptr(unsigned n) { return reinterpret_cast<size_t*>((size_t)(n << 4) + 3); }
        bool is_literal(size_t* p) { return (reinterpret_cast<size_t>(p) & 3) == 0; }
        bool is_index(size_t* p) { return (reinterpret_cast<size_t>(p) & 3) == 3; }
        bool is_enode(size_t* p) { return (reinterpret_cast<size_t>(p) & 3) == 1; }
        sat::literal to_literal(size_t* p) { return sat::to_literal(static_cast<unsigned>(reinterpret_cast<size_t>(p) >> 4)); };
        euf::enode* to_enode(size_t* p) { return reinterpret_cast<euf::enode*>(reinterpret_cast<size_t>(p) >> 4); }
        unsigned to_index(size_t* p) { return static_cast<unsigned>(reinterpret_cast<size_t>(p) >> 4); }
        
    public:
        array_plugin(context& ctx);
        ~array_plugin() override {}
        void register_term(expr* e) override { if (a.is_array(e->get_sort())) m_has_arrays = true; }
        expr_ref get_value(expr* e) override;
        void initialize() override { m_g = nullptr; }
        void propagate_literal(sat::literal lit) override { m_g = nullptr; }
        bool propagate() override { return false; }
        bool repair_down(app* e) override { return true; }
        void repair_up(app* e) override {}
        void repair_literal(sat::literal lit) override { m_g = nullptr; }
        bool is_sat() override;

        void on_rescale() override {}
        void on_restart() override {}
        std::ostream& display(std::ostream& out) const override;
        bool set_value(expr* e, expr* v) override { return false; }
        void collect_statistics(statistics& st) const override;
        void reset_statistics() override { m_stats.reset(); }
    };

}
