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
        m_add(g, "add", get_id(), OP_ADD),
        m_mul(g, "mul", get_id(), OP_MUL) {
        std::function<void(void)> uadd = [&]() { m_undo.push_back(undo_t::undo_add); };
        m_add.set_undo(uadd);
        std::function<void(void)> umul = [&]() { m_undo.push_back(undo_t::undo_mul); };
        m_mul.set_undo(umul);
        m_add.set_injective();
        auto e = a.mk_int(0);
        auto n = g.find(e) ? g.find(e) : g.mk(e, 0, 0, nullptr);
        m_add.add_unit(n);
        m_mul.add_zero(n);

        e = a.mk_real(0);
        n = g.find(e) ? g.find(e) : g.mk(e, 0, 0, nullptr);
        m_add.add_unit(n);
        m_mul.add_zero(n);

        e = a.mk_int(1);
        n = g.find(e) ? g.find(e) : g.mk(e, 0, 0, nullptr);
        m_mul.add_unit(n);

        e = a.mk_real(1);
        n = g.find(e) ? g.find(e) : g.mk(e, 0, 0, nullptr);
        m_mul.add_unit(n);


    }    

    void arith_plugin::register_node(enode* n) {
        TRACE(plugin, tout << g.bpp(n) << "\n");
        m_add.register_node(n);
        m_mul.register_node(n);
        expr* e = n->get_expr(), * x, * y;
        // x - y = x + (* -1 y)
        if (a.is_sub(e, x, y)) {
            auto& m = g.get_manager();
            auto e1 = a.mk_numeral(rational(-1), a.is_int(x));
            auto n1 = g.find(e1) ? g.find(e1) : g.mk(e1, 0, 0, nullptr);
            auto e2 = a.mk_mul(e1, y);
            enode* es1[2] = { n1, g.find(y)};
            auto mul = g.find(e2) ? g.find(e2) : g.mk(e2, 0, 2, es1);
            enode* es2[2] = { g.find(x), mul };
            expr* e_add = a.mk_add(x, e2);
            auto add = g.find(e_add) ? g.find(e_add): g.mk(e_add, 0, 2, es2);
            push_merge(n, add);
        }
        // c1 * c2 = c1*c2
        rational r1, r2;
        if (a.is_mul(e, x, y) && a.is_numeral(x, r1) && a.is_numeral(y, r2)) {
            rational r = r1 * r2;
            auto e1 = a.mk_numeral(r, a.is_int(x));
            auto n1 = g.find(e1) ? g.find(e1) : g.mk(e1, 0, 0, nullptr);
            push_merge(n, n1);
        }
        if (a.is_uminus(e, x)) {
            NOT_IMPLEMENTED_YET();
        }

    }

    void arith_plugin::merge_eh(enode* n1, enode* n2) {
        TRACE(plugin, tout << g.bpp(n1) << " == " << g.bpp(n2) << "\n");
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
        m_add.display(out);
        m_mul.display(out);
        return out;
    }
}
