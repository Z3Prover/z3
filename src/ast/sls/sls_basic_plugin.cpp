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
        if (m.is_ite(e) && !m.is_bool(e))
            return true;
        if (m.is_xor(e) && to_app(e)->get_num_args() != 2)
            return true;
        if (m.is_distinct(e))
            return true;
        return false;        
    }

    void basic_plugin::propagate_literal(sat::literal lit) {
    }

    void basic_plugin::register_term(expr* e) {
        expr* c, * th, * el;
        if (m.is_ite(e, c, th, el) && !m.is_bool(e)) {
            auto eq_th = expr_ref(m.mk_eq(e, th), m);
            auto eq_el = expr_ref(m.mk_eq(e, el), m);

            ctx.add_theory_axiom(m.mk_or(mk_not(m, c), eq_th));
            ctx.add_theory_axiom(m.mk_or(c, eq_el));
#if 0
            auto eq_th_el = expr_ref(m.mk_eq(th, el), m);
            verbose_stream() << mk_bounded_pp(eq_th_el, m) << "\n";
            ctx.add_theory_axiom(m.mk_or(eq_th_el, c, m.mk_not(eq_th)));
            ctx.add_theory_axiom(m.mk_or(eq_th_el, m.mk_not(c), m.mk_not(eq_el)));
#endif
        }
    }

    void basic_plugin::initialize() {
    }

    bool basic_plugin::propagate() {
        return false;
    }

    bool basic_plugin::is_sat() {
        return true;
    }

    std::ostream& basic_plugin::display(std::ostream& out) const {
        return out;
    }

    bool basic_plugin::set_value(expr* e, expr* v) {
        if (!m.is_bool(e))
            return false;
        SASSERT(m.is_true(v) || m.is_false(v));
        return set_value(e, m.is_true(v));
    }

    expr_ref basic_plugin::eval_ite(app* e) {
        expr* c = nullptr, * th = nullptr, * el = nullptr;
        VERIFY(m.is_ite(e, c, th, el));
        if (bval0(c))
            return ctx.get_value(th);
        else
            return ctx.get_value(el);       
    }

    expr_ref basic_plugin::eval_distinct(app* e) {
        for (unsigned i = 0; i < e->get_num_args(); ++i) {
            for (unsigned j = i + 1; j < e->get_num_args(); ++j) {
                if (bval0(e->get_arg(i)) == bval0(e->get_arg(j)))
                    return expr_ref(m.mk_false(), m);
            }
        }
        return expr_ref(m.mk_true(), m);
    }

    expr_ref basic_plugin::eval_xor(app* e) {
        bool b = false;
        for (expr* arg : *e)
            b ^= bval0(arg);
        return expr_ref(m.mk_bool_val(b), m);
    }

    bool basic_plugin::bval0(expr* e) const {
        SASSERT(m.is_bool(e));     
        return ctx.is_true(e);
    }

    bool basic_plugin::try_repair(app* e, unsigned i) {
        switch (e->get_decl_kind()) {
        case OP_XOR:
            return try_repair_xor(e, i);
        case OP_ITE:
            return try_repair_ite(e, i);
        case OP_DISTINCT:
            return try_repair_distinct(e, i);
        default:            
            return true;
        }
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
        if (m.is_bool(e))
            return true;
        auto child = e->get_arg(i);
        auto cond = e->get_arg(0);
        bool c = bval0(cond);

        if (i == 0) {
            auto eval = ctx.get_value(e);
            auto eval1 = ctx.get_value(e->get_arg(1));
            auto eval2 = ctx.get_value(e->get_arg(2));
            if (eval == eval1 && eval == eval2)
                return true;
            if (eval == eval1)
                return set_value(cond, true);
            if (eval == eval2)
                return set_value(cond, false);
            return false;
        }
        if (c != (i == 1))
            return false;
        if (m.is_value(child))
            return false;
        bool r = ctx.set_value(child, ctx.get_value(e));
        return r;
    }

    void basic_plugin::repair_up(app* e) {
        expr* c, * th, * el;
        expr_ref val(m);
        if (!is_basic(e))
            return;
        if (m.is_ite(e, c, th, el) && !m.is_bool(e)) 
            val = eval_ite(e);        
        else if (m.is_xor(e)) 
            val = eval_xor(e);        
        else if (m.is_distinct(e)) 
            val = eval_distinct(e);           
        else
            return;
        if (!ctx.set_value(e, val))
            ctx.new_value_eh(e);
    }

    void basic_plugin::repair_literal(sat::literal lit) {
    }

    bool basic_plugin::repair_down(app* e) {    
        if (!is_basic(e))
            return true;     

        if (m.is_xor(e) && eval_xor(e) == ctx.get_value(e))
            return true;
        if (m.is_ite(e) && !m.is_bool(e)) {
            if (eval_ite(e) == ctx.get_value(e))
                return true;
            if (try_repair(e, 1))
                return true;
            if (try_repair(e, 2))
                return true;
            ctx.flip(ctx.atom2bool_var(e->get_arg(0)));
            return true;
        }
        if (m.is_distinct(e) && eval_distinct(e) == ctx.get_value(e))
            return true;
        unsigned n = e->get_num_args();
        unsigned s = ctx.rand(n);
        for (unsigned i = 0; i < n; ++i) {
            auto j = (i + s) % n;
            if (try_repair(e, j)) 
                return true;            
        }
        return false;
    }

    bool basic_plugin::try_repair_distinct(app* e, unsigned i) {
        NOT_IMPLEMENTED_YET();
        return false;
    }

    bool basic_plugin::set_value(expr* e, bool b) {
        auto lit = ctx.mk_literal(e);
        if (ctx.is_true(lit) != b) {
            ctx.flip(lit.var());
            ctx.new_value_eh(e);
        }
        return true;
    }
}
