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
#include "ast/ast_pp.h"
#include "ast/ast_util.h"

namespace sls {

    expr_ref basic_plugin::get_value(expr* e) {
        return expr_ref(m.mk_bool_val(bval0(e)), m);
    }

    bool basic_plugin::is_basic(expr* e) const {
        if (!e || !is_app(e))
            return false;
        if (to_app(e)->get_family_id() != basic_family_id)
            return false;
        if (!m.is_bool(e))
            return false;
        expr* x, * y;
        if (m.is_eq(e, x, y) && !m.is_bool(x))
            return false;
        if (m.is_distinct(e) && !m.is_bool(to_app(e)->get_arg(0)))
            return false;
        return true;
    }

    void basic_plugin::propagate_literal(sat::literal lit) {
        auto a = ctx.atom(lit.var());
        if (!is_basic(a))
            return;
        if (bval1(to_app(a)) != bval0(to_app(a)))
            ctx.new_value_eh(a);
    }

    void basic_plugin::register_term(expr* e) {
        if (is_basic(e))
            m_values.setx(e->get_id(), bval1(to_app(e)), false);
    }

    void basic_plugin::initialize() {
    }

    bool basic_plugin::propagate() {
        for (auto t : ctx.subterms())
            if (is_basic(t) && !m.is_not(t) && 
                bval0(t) != bval1(to_app(t))) {
                add_clause(to_app(t));
                return true;
            }

        return false;
    }

    bool basic_plugin::is_sat() {
        for (auto t : ctx.subterms())
            if (is_basic(t) && !m.is_not(t) && 
                bval0(t) != bval1(to_app(t))) {
                verbose_stream() << mk_bounded_pp(t, m) << " := " << (bval0(t) ? "T" : "F") << " eval: " << (bval1(to_app(t)) ? "T" : "F") << "\n";
                return false;
            }
        return true;
    }


    std::ostream& basic_plugin::display(std::ostream& out) const {
        for (auto t : ctx.subterms())
            if (is_basic(t))
                out << mk_bounded_pp(t, m) << " := " << (bval0(t)?"T":"F") << " eval: " << (bval1(to_app(t))?"T":"F") << "\n";
        return out;
    }

    void basic_plugin::set_value(expr* e, expr* v) {
        if (!is_basic(e))
            return;
        SASSERT(m.is_true(v) || m.is_false(v));
        set_value(e, m.is_true(v));
    }

    bool basic_plugin::bval1(app* e) const {
        if (m.is_not(e))
            return bval1(to_app(e->get_arg(0)));
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
            verbose_stream() << mk_bounded_pp(e, m) << " " << ctx.get_value(a) << " " << ctx.get_value(b) << "\n";
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
        bool b = true;
        while (m.is_not(e, e))
            b = !b;
        sat::bool_var v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var)
            return b == m_values.get(e->get_id(), false);
        else
            return b == ctx.is_true(v);
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
            return try_repair_distinct(e, i);
        default:
            UNREACHABLE();
            return false;
        }
    }

    void basic_plugin::add_clause(app* e) {
        expr_ref_vector es(m);
        expr_ref fml(m);
        expr* x, *y;
        switch (e->get_decl_kind()) {
        case OP_AND:
            for (expr* arg : *e) {
                ctx.add_constraint(m.mk_or(m.mk_not(e), arg));
                es.push_back(mk_not(m, arg));
            }
            es.push_back(e);
            ctx.add_constraint(m.mk_or(es));
            break;
        case OP_OR:            
            for (expr* arg : *e) {
                ctx.add_constraint(m.mk_or(mk_not(m, arg), e));
                es.push_back(arg);                
            }
            es.push_back(m.mk_not(e));
            ctx.add_constraint(m.mk_or(es));
            break;
        case OP_NOT:
            break;
        case OP_FALSE:
            break;
        case OP_TRUE:
            break;
        case OP_EQ:
            VERIFY(m.is_eq(e, x, y));
            ctx.add_constraint(m.mk_or(m.mk_not(e), mk_not(m, x), y));
            ctx.add_constraint(m.mk_or(m.mk_not(e), mk_not(m, y), x));
            ctx.add_constraint(m.mk_or(e, y, x));
            ctx.add_constraint(m.mk_or(e, mk_not(m, x), mk_not(m, y)));
            break;
        case OP_IMPLIES:
            NOT_IMPLEMENTED_YET();
        case OP_XOR:
            NOT_IMPLEMENTED_YET();
        case OP_ITE:
            NOT_IMPLEMENTED_YET();
        case OP_DISTINCT:
            NOT_IMPLEMENTED_YET();
        default:
            UNREACHABLE();
            break;
        }
        
    }


    bool basic_plugin::try_repair_and_or(app* e, unsigned i) {
        auto b = bval0(e);
        if ((b && m.is_and(e)) || (!b && m.is_or(e))) {
            for (auto arg : *e)
                if (!set_value(arg, b))
                    return false;
            return true;
        }      
        auto child = e->get_arg(i);
        if (b == bval0(child))
            return false;
        return set_value(child, b);
    }

    bool basic_plugin::try_repair_not(app* e) {
        auto child = e->get_arg(0);
        return set_value(child, !bval0(e));
    }

    bool basic_plugin::try_repair_eq(app* e, unsigned i) {
        auto child = e->get_arg(i);
        auto sibling = e->get_arg(1 - i);
        if (!m.is_bool(child))
            return false;
        return set_value(child, bval0(e) == bval0(sibling));
    }

    bool basic_plugin::try_repair_xor(app* e, unsigned i) {
        auto child = e->get_arg(i);
        bool bv = false;
        for (unsigned j = 0; j < e->get_num_args(); ++j)
            if (j != i)
                bv ^= bval0(e->get_arg(j));
        bool ev = bval0(e);
        return set_value(child, ev != bv);
    }

    bool basic_plugin::try_repair_ite(app* e, unsigned i) {
        if (!m.is_bool(e))
            return false;
        auto child = e->get_arg(i);
        auto cond = e->get_arg(0);
        bool c = bval0(cond);
        if (i == 0) {
            if (ctx.rand(2) == 0)        
                return set_value(cond, true) && set_value(e->get_arg(1), bval0(e));
            else
                return set_value(cond, false) && set_value(e->get_arg(2), bval0(e));
        }

        if (!set_value(child, bval0(e)))
            return false;
        return (c == (i == 1)) || set_value(cond, !c);                  
    }

    bool basic_plugin::try_repair_implies(app* e, unsigned i) {
        auto child = e->get_arg(i);
        auto sibling = e->get_arg(1 - i);
        bool ev = bval0(e);
        bool av = bval0(child);
        bool bv = bval0(sibling);
        if (ev) {

            if (i == 0 && (!av || bv))
                return true;
            if (i == 1 && (!bv || av))
                return true;
            if (i == 0) {
                return set_value(child, false);
            }
            if (i == 1) {
                return set_value(child, true);
            }
            return false;
        }
        if (i == 0 && av && !bv)
            return true;
        if (i == 1 && bv && !av)
            return true;
        if (i == 0) 
            return set_value(child, true) && set_value(sibling, false);        
        if (i == 1) 
            return set_value(child, false) && set_value(sibling, true);                  
        return false;
    }

    void basic_plugin::repair_up(app* e) {
        if (!is_basic(e))
            return;
        auto b = bval1(e);
        if (bval0(e) == b)
            return;
        set_value(e, b);
    }

    bool basic_plugin::repair_down(app* e) {
        SASSERT(m.is_bool(e));
        unsigned n = e->get_num_args();
        if (!is_basic(e))
            return false;
        if (n == 0) 
            return true;
        
        if (bval0(e) == bval1(e))
            return true;
        unsigned s = ctx.rand(n);
        for (unsigned i = 0; i < n; ++i) {
            auto j = (i + s) % n;
            if (try_repair(e, j)) 
                return true;            
        }
        return false;
    }

    bool basic_plugin::try_repair_distinct(app* e, unsigned i) {
        return false;
    }

    bool basic_plugin::set_value(expr* e, bool b) {
        if (m.is_true(e) && !b)
            return false;
        if (m.is_false(e) && b)
            return false;
        sat::bool_var v = ctx.atom2bool_var(e);
        if (v == sat::null_bool_var) {
            if (m_values.get(e->get_id(), b) != b) {
                m_values.set(e->get_id(), b);
                ctx.new_value_eh(e);
            }
        }
        else if (ctx.is_true(v) != b) {
            ctx.flip(v);
            ctx.new_value_eh(e);
        }
        return true;
    }
}
