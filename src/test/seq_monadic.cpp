/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic.cpp

Abstract:

    Unit tests for the whole-language monadic-decomposition membership solver in
    ast/rewriter/seq_monadic.cpp.  Mirrors the validated Python prototype
    (files/solve_proto.py): single-variable repeated-membership shapes  x.a.x in R.

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_monadic.h"
#include <iostream>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_monadic_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    seq_monadic      m_mon;
    seq_util         u;
    sort_ref         m_str;   // String sort
    sort_ref         m_re;    // RegEx sort over m_str
    unsigned         m_fail = 0;

    seq_util::rex& re() { return u.re; }

    // regex builders
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref inter(expr* a, expr* b) { return expr_ref(re().mk_inter(a, b), m); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref dotstar() { return expr_ref(re().mk_full_seq(m_re), m); }
    expr_ref rng(char lo, char hi) {
        char sl[2] = { lo, 0 }, sh[2] = { hi, 0 };
        return expr_ref(re().mk_range(u.str.mk_string(zstring(sl)), u.str.mk_string(zstring(sh))), m);
    }
    expr_ref loop(expr* r, unsigned lo, unsigned hi) { return expr_ref(re().mk_loop(r, lo, hi), m); }

    // string-term builders
    expr_ref var(char const* nm) { return expr_ref(m.mk_const(nm, m_str), m); }
    expr_ref sword(char const* s) { return expr_ref(u.str.mk_string(zstring(s)), m); }
    expr_ref sconcat(expr* a, expr* b) { return expr_ref(u.str.mk_concat(a, b), m); }
    // term  x . w . x  (w a constant word)
    expr_ref xwx(expr* x, char const* w) { return sconcat(x, sconcat(sword(w), x)); }
    // term  x . a . y  (two distinct variables)
    expr_ref xay(expr* x, expr* y) { return sconcat(x, sconcat(sword("a"), y)); }
    // term  x . y . x
    expr_ref xyx(expr* x, expr* y) { return sconcat(x, sconcat(y, x)); }

    static char const* s(lbool l) { return l == l_true ? "sat" : l == l_false ? "unsat" : "undef"; }

    void check(char const* name, expr* term, expr* R, lbool expected) {
        lbool got = m_mon.solve(term, R);
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    void check_extra(char const* name, expr* term, expr* R,
                     obj_map<expr, expr*> const& ve, lbool expected) {
        lbool got = m_mon.solve(term, R, ve);
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

public:
    seq_monadic_test() : m_reg(m), m_rw(m), m_mon(m_rw), u(m), m_str(m), m_re(m) {
        m_str = u.str.mk_string_sort();
        m_re  = re().mk_re(m_str);
    }

    void run() {
        expr_ref x  = var("x");
        expr_ref a  = word("a");
        expr_ref b  = word("b");
        expr_ref ab = cat(a, b);
        expr_ref sig = dotstar();                                   // Sigma*
        expr_ref saas = cat(sig, cat(cat(a, a), sig));              // Sigma* a a Sigma*
        expr_ref sbbs = cat(sig, cat(cat(b, b), sig));              // Sigma* b b Sigma*

        std::cout << "=== seq_monadic: single-variable membership (x.a.x in R) ===\n";

        // sanity
        check("(a|b)*        x.a.x", xwx(x, "a"), star(alt(a, b)), l_true);
        check("b*            x.a.x", xwx(x, "a"), star(b), l_false);
        check("Sig*aaSig*    x.a.x", xwx(x, "a"), saas, l_true);
        check("x in (a|b)*        ", x, star(alt(a, b)), l_true);
        check("x in b* (x=aa)     ", xwx(x, "a"), star(b), l_false);

        // ALT = (a|b)* & ~(Sig*aaSig*) & ~(Sig*bbSig*)  (strictly alternating)
        expr_ref altre = inter(star(alt(a, b)), inter(comp(saas), comp(sbbs)));
        check("ALT           x.a.x", xwx(x, "a"), altre, l_true);

        // R*.S complement family
        check("~(a*.b)       x.a.x", xwx(x, "a"), comp(cat(star(a), b)), l_true);

        // L3-02 ~((ab)*.~((ab)*))   -> unsat (odd length)
        check("L3-02         x.a.x", xwx(x, "a"),
              comp(cat(star(ab), comp(star(ab)))), l_false);

        // L3-03 ~(a*.~(b*.~((ab)*)))  -> sat
        check("L3-03         x.a.x", xwx(x, "a"),
              comp(cat(star(a), comp(cat(star(b), comp(star(ab)))))), l_true);

        std::cout << "=== seq_monadic: multi-variable ===\n";
        expr_ref y = var("y");
        check("(a|b)*        x.a.y", xay(x, y), star(alt(a, b)), l_true);
        check("b*            x.a.y", xay(x, y), star(b), l_false);
        check("L3-02         x.a.y", xay(x, y), comp(cat(star(ab), comp(star(ab)))), l_true);
        check("L3-03         x.a.y", xay(x, y),
              comp(cat(star(a), comp(cat(star(b), comp(star(ab)))))), l_true);
        check("empty ~Sig*   x.y.x", xyx(x, y), comp(dotstar()), l_false);
        check("Sig*          x.y.x", xyx(x, y), dotstar(), l_true);
        check("(a|b)*        x.y.x", xyx(x, y), star(alt(a, b)), l_true);

        std::cout << "=== seq_monadic: per-variable constraints ===\n";
        expr_ref digitp = cat(rng('0', '9'), star(rng('0', '9')));   // [0-9]+
        obj_map<expr, expr*> ve;
        ve.insert(y, digitp);
        // y must be in the (a|b)* tail AND in [0-9]+  -> empty -> unsat
        check_extra("(a|b)* & y in[0-9]+ x.a.y", xay(x, y), star(alt(a, b)), ve, l_false);
        // y any digits, x/'a' anything -> sat
        check_extra("Sig*   & y in[0-9]+ x.a.y", xay(x, y), dotstar(), ve, l_true);

        // Bounded loop (re.loop) with repeated variable -- exercises live_states on a
        // counted automaton (t04-exact benchmark family).  Regression for a
        // reference-invalidation bug in live_states (succ[i].push_back(intern(t))).
        std::cout << "=== seq_monadic: bounded loop (t04-exact family) ===\n";
        expr_ref clsr    = rng('0', '9');                            // [0-9]
        expr_ref digitS  = star(clsr);                               // [0-9]*
        expr_ref loop22  = loop(clsr, 2, 2);                         // [0-9]{2}
        check("[0-9]{2}      x    ", x, loop22, l_true);             // x = "00"
        check("[0-9]{2}      x.a.x", xwx(x, "a"), loop22, l_false);  // 'a' not a digit
        obj_map<expr, expr*> ve2; ve2.insert(x, digitp); ve2.insert(y, digitS);
        // x.y.x in [0-9]{2}, x in [0-9]+, y in [0-9]*  -> sat (x="0", y="")
        check_extra("[0-9]{2} & x[0-9]+ y[0-9]* x.y.x", xyx(x, y), loop22, ve2, l_true);
        obj_map<expr, expr*> ve3; ve3.insert(x, digitp);
        check_extra("[0-9]{2} & x[0-9]+       x.y.x", xyx(x, y), loop22, ve3, l_true);
        obj_map<expr, expr*> ve4; ve4.insert(x, digitp);
        // x.y.x in [0-9]{3}, x in [0-9]+ -> sat (x=1 digit, y=1 digit)
        check_extra("[0-9]{3} & x[0-9]+       x.y.x", xyx(x, y), loop(clsr, 3, 3), ve4, l_true);

        std::cout << "=== seq_monadic: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_monadic() {
    seq_monadic_test t;
    t.run();
}
