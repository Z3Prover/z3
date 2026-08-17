/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_parikh.cpp

Abstract:

    Unit tests for the Parikh-image filter in ast/rewriter/seq_parikh.cpp.

Author:

    Clemens Eisenhofer 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_parikh.h"
#include <iostream>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_parikh_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    trail_stack      m_trail;
    seq_parikh       m_parikh;
    seq_util         u;
    sort_ref         m_str;
    unsigned         m_fail = 0;

    expr_ref var(char const* nm) { return expr_ref(m.mk_const(nm, m_str), m); }
    expr_ref lit(char const* s) { return expr_ref(u.str.mk_string(zstring(s)), m); }
    expr_ref unit(expr* c) { return expr_ref(u.str.mk_unit(c), m); }
    expr_ref chr(unsigned c) { return expr_ref(u.mk_char(c), m); }

    expr_ref cat(std::initializer_list<expr*> es) {
        expr_ref r(u.str.mk_empty(m_str), m);
        for (expr* e : es) {
            r = u.str.mk_concat(r, e);
        }
        return r;
    }

    void expect(char const* descr, lbool actual, lbool expected) {
        bool ok = actual == expected;
        if (!ok)
            ++m_fail;
        std::cout << (ok ? "PASS " : "FAIL ") << descr
                  << " (got " << actual << ", expected " << expected << ")\n";
    }

    void check_eq(char const* descr, expr* lhs, expr* rhs, lbool expected) {
        expect(descr, m_parikh.check_eq(lhs, rhs), expected);
    }

public:
    seq_parikh_test() :
        m_reg(m), m_rw(m), m_parikh(m_rw, m_trail), u(m),
        m_str(u.str.mk_string_sort(), m) {}

    void run() {
        expr_ref x = var("x"), y = var("y");
        expr_ref a = lit("a"), b = lit("b"), ab = lit("ab"), ba = lit("ba");
        expr_ref c = chr('c');

        // opaque tokens cancel
        check_eq("x.ab.y = y.ba.x", cat({x, ab, y}), cat({y, ba, x}), l_undef);
        check_eq("x.a = b.x", cat({x, a}), cat({b, x}), l_false);
        check_eq("x.ab.y = y.ab.b.x", cat({x, ab, y}), cat({y, ab, b, x}), l_false);
        check_eq("x.a.a = a.x", cat({x, a, a}), cat({a, x}), l_false);
        check_eq("x.x.a.b = b.a.x.x", cat({x, x, a, b}), cat({b, a, x, x}), l_undef);
        check_eq("x.eps.a = a.x", cat({x, a}), cat({a, x}), l_undef);

        // opaque tokens do not cancel, so the constants are not compared
        check_eq("x.a = y.b", cat({x, a}), cat({y, b}), l_undef);
        check_eq("x.x.a = x.b", cat({x, x, a}), cat({x, b}), l_undef);

        // ground equations: the Parikh image is decided, the word is not
        check_eq("ab = ba", ab, ba, l_undef);
        check_eq("ab = a", ab, a, l_false);

        // a symbolic unit is opaque, a unit of a character value is constant
        expr_ref su = unit(m.mk_const("sc", u.mk_char_sort()));
        check_eq("su.a = su.b", cat({su, a}), cat({su, b}), l_false);
        check_eq("su.a = a", cat({su, a}), a, l_undef);
        check_eq("unit(c).a = a.unit(c)", cat({unit(c), a}), cat({a, unit(c)}), l_undef);
        check_eq("unit(c).a = a.a", cat({unit(c), a}), cat({a, a}), l_false);

        void* d1 = reinterpret_cast<void*>(1);
        m_parikh.add_eq(cat({x, ab, y}), cat({y, ba, x}), nullptr);
        expect("check() without a refutable equation", m_parikh.check(), l_undef);
        m_parikh.add_eq(cat({x, a}), cat({b, x}), d1);
        expect("check() with a refutable equation", m_parikh.check(), l_false);

        bool core_ok = m_parikh.core().size() == 1 && m_parikh.core()[0] == d1;
        if (!core_ok)
            ++m_fail;
        std::cout << (core_ok ? "PASS " : "FAIL ") << "core is the refuted equation\n";

        std::cout << "=== seq_parikh: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_parikh() {
    seq_parikh_test t;
    t.run();
}
