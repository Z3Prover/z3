/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_basic_plugin.cpp

Abstract:

    Local search dispatch for Boolean connectives

Author:

    Nikolaj Bjorner (nbjorner) 2024-07-07

--*/

#include "ast/sls/sls_basic_plugin.h"
#include "ast/ast_ll_pp.h"

namespace sls {

    expr_ref basic_plugin::get_value(expr* e) {
        return expr_ref(m.mk_bool_val(bval0(e)), m);
    }

    lbool basic_plugin::check() {
        init();
        for (sat::literal lit : ctx.root_literals())
            repair_literal(lit);
        repair_defs_and_updates();
        return ctx.unsat().empty() ? l_true : l_undef;
    }

    void basic_plugin::init() {
        m_repair_down = UINT_MAX;
        m_repair_roots.reset();
        m_repair_up.reset();
        if (m_initialized)
            return;
        m_initialized = true;
        for (auto t : ctx.subterms())
            if (is_app(t) && m.is_bool(t) && to_app(t)->get_family_id() == basic_family_id)
                m_values.setx(t->get_id(), bval1(to_app(t)), false);
    }

    bool basic_plugin::is_sat() {
        for (auto t : ctx.subterms())
            if (is_app(t) && 
                m.is_bool(t) && 
                to_app(t)->get_family_id() == basic_family_id && 
                bval0(t) != bval1(to_app(t)))
                    return false;
        return true;
    }


    std::ostream& basic_plugin::display(std::ostream& out) const {
        for (auto t : ctx.subterms())
            if (is_app(t) && m.is_bool(t) && to_app(t)->get_family_id() == basic_family_id)
                out << mk_bounded_pp(t, m) << " " << bval0(t) << " ~ " << bval1(to_app(t)) << "\n";
        return out;
    }

    void basic_plugin::set_value(expr* e, expr* v) {
        if (!m.is_bool(e))
            return;
        SASSERT(m.is_bool(v));
        SASSERT(m.is_true(v) || m.is_false(v));
        if (bval0(e) != m.is_true(v))
            return;
        set_value(e, m.is_true(v));
        m_repair_roots.insert(e->get_id());
    }

    bool basic_plugin::bval1(app* e) const {
        SASSERT(m.is_bool(e));
        SASSERT(e->get_family_id() == basic_family_id);

        auto id = e->get_id();
        switch (e->get_decl_kind()) {
        case OP_TRUE:
            return true;
        case OP_FALSE:
            return false;
        case OP_AND:
            return all_of(*to_app(e), [&](expr* arg) { return bval0(arg); });
        case OP_OR:
            return any_of(*to_app(e), [&](expr* arg) { return bval0(arg); });
        case OP_NOT:
            return !bval0(e->get_arg(0));
        case OP_XOR: {
            bool r = false;
            for (auto* arg : *to_app(e))
                r ^= bval0(arg);
            return r;
        }
        case OP_IMPLIES: {
            auto a = e->get_arg(0);
            auto b = e->get_arg(1);
            return !bval0(a) || bval0(b);
        }
        case OP_ITE: {
            auto c = bval0(e->get_arg(0));
            return bval0(c ? e->get_arg(1) : e->get_arg(2));
        }
        case OP_EQ: {
            auto a = e->get_arg(0);
            auto b = e->get_arg(1);
            if (m.is_bool(a))
                return bval0(a) == bval0(b);
            return ctx.get_value(a) == ctx.get_value(b);
        }
        case OP_DISTINCT: {
            for (unsigned i = 0; i < e->get_num_args(); ++i)
                for (unsigned j = i + 1; j < e->get_num_args(); ++j)
                    if (ctx.get_value(e->get_arg(i)) == ctx.get_value(e->get_arg(j)))
                        return false;
            return true;
        }
        default:
            verbose_stream() << mk_bounded_pp(e, m) << "\n";
            UNREACHABLE();
            break;
        }
        UNREACHABLE();
        return false;
    }

    bool basic_plugin::bval0(expr* e) const {
        SASSERT(m.is_bool(e));
        sat::bool_var v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var)
            return m_values.get(e->get_id(), false);
        else
            return ctx.is_true(sat::literal(v, false));
    }

    bool basic_plugin::try_repair(app* e, unsigned i) {
        switch (e->get_decl_kind()) {
        case OP_AND:
            return try_repair_and_or(e, i);
        case OP_OR:
            return try_repair_and_or(e, i);
        case OP_NOT:
            return try_repair_not(e);
        case OP_FALSE:
            return false;
        case OP_TRUE:
            return false;
        case OP_EQ:
            return try_repair_eq(e, i);
        case OP_IMPLIES:
            return try_repair_implies(e, i);
        case OP_XOR:
            return try_repair_xor(e, i);
        case OP_ITE:
            return try_repair_ite(e, i);
        case OP_DISTINCT:
            NOT_IMPLEMENTED_YET();
            return false;
        default:
            UNREACHABLE();
            return false;
        }
    }

    bool basic_plugin::try_repair_and_or(app* e, unsigned i) {
        auto b = bval0(e);
        auto child = e->get_arg(i);
        if (b == bval0(child))
            return false;
        set_value(child, b);
        return true;
    }

    bool basic_plugin::try_repair_not(app* e) {
        auto child = e->get_arg(0);
        set_value(child, !bval0(e));
        return true;
    }

    bool basic_plugin::try_repair_eq(app* e, unsigned i) {
        auto child = e->get_arg(i);
        auto sibling = e->get_arg(1 - i);
        if (!m.is_bool(child))
            return false;
        set_value(child, bval0(e) == bval0(sibling));
        return true;
    }

    bool basic_plugin::try_repair_xor(app* e, unsigned i) {
        bool ev = bval0(e);
        bool bv = bval0(e->get_arg(1 - i));
        auto child = e->get_arg(i);
        set_value(child, ev != bv);
        return true;
    }

    bool basic_plugin::try_repair_ite(app* e, unsigned i) {
        auto child = e->get_arg(i);
        bool c = bval0(e->get_arg(0));
        if (i == 0) {
            set_value(child, !c);
            return true;
        }
        if (c != (i == 1))
            return false;
        if (m.is_bool(e)) {
            set_value(child, bval0(e));
            return true;
        }
        return false;
    }

    bool basic_plugin::try_repair_implies(app* e, unsigned i) {
        auto child = e->get_arg(i);
        bool ev = bval0(e);
        bool av = bval0(child);
        bool bv = bval0(e->get_arg(1 - i));
        if (i == 0) {
            if (ev == (!av || bv))
                return false;
        }
        else if (ev != (!bv || av))
            return false;
        set_value(child, ev);
        return true;
    }

    bool basic_plugin::repair_up(expr* e) {
        if (!m.is_bool(e))
            return false;
        auto b = bval1(to_app(e));
        set_value(e, b);
        return true;
    }

    void basic_plugin::repair_down(app* e) {
        SASSERT(m.is_bool(e));
        unsigned n = e->get_num_args();
        if (n == 0 || e->get_family_id() != m.get_basic_family_id()) {
            for (auto p : ctx.parents(e))               
                m_repair_up.insert(p->get_id());
            ctx.set_value(e, m.mk_bool_val(bval0(e)));
            return;
        }
        if (bval0(e) == bval1(e))
            return;
        unsigned s = ctx.rand(n);
        for (unsigned i = 0; i < n; ++i) {
            auto j = (i + s) % n;
            if (try_repair(e, j)) {
                m_repair_down = e->get_arg(j)->get_id();
                return;
            }
        }
        m_repair_up.insert(e->get_id());
    }


    void basic_plugin::repair_defs_and_updates() {
        if (!m_repair_roots.empty() ||
            !m_repair_up.empty() ||
            m_repair_down != UINT_MAX) {

            while (m_repair_down != UINT_MAX) {
                auto e = ctx.term(m_repair_down);
                repair_down(to_app(e));
            }

            while (!m_repair_up.empty()) {
                auto id = m_repair_up.elem_at(rand() % m_repair_up.size());
                auto e = ctx.term(id);
                m_repair_up.remove(id);
                repair_up(to_app(e));
            }

            if (!m_repair_roots.empty()) {
                auto id = m_repair_roots.elem_at(rand() % m_repair_roots.size());
                m_repair_roots.remove(id);
                m_repair_down = id;
            }
        }
    }

    void basic_plugin::set_value(expr* e, bool b) {
        sat::bool_var v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var) {
            if (m_values.get(e->get_id(), b) != b) {
                m_values.set(e->get_id(), b);
                ctx.set_value(e, m.mk_bool_val(b));
            }
        }
        else if (ctx.is_true(sat::literal(v, false)) != b) {
            ctx.flip(v);
            ctx.set_value(e, m.mk_bool_val(b));
        }
    }

    void basic_plugin::repair_literal(sat::literal lit) {
        if (!ctx.is_true(lit))
            return;
        auto a = ctx.atom(lit.var());
        if (!a || !is_app(a))
            return;
        if (to_app(a)->get_family_id() != basic_family_id)
            return;
        if (bval1(to_app(a)) != bval0(to_app(a)))
            m_repair_roots.insert(a->get_id());
    }

}
