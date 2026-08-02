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
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_monadic.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "params/smt_params.h"
#include "smt/smt_kernel.h"
#include <iostream>
#include <set>

namespace {

struct plugin_registrar {
    plugin_registrar(ast_manager& m) { reg_decl_plugins(m); }
};

class seq_monadic_test {
    ast_manager      m;
    plugin_registrar m_reg;
    seq_rewriter     m_rw;
    trail_stack      m_trail;
    seq_monadic      m_mon;
    seq_util         u;
    sort_ref         m_str;   // String sort
    sort_ref         m_re;    // RegEx sort over m_str
    seq_monadic::transition_mode m_mode;
    u_dependency_manager m_dm;   // owns the leaf dependencies used in unsat-core tests
    unsigned         m_fail = 0;

    seq_util::rex& re() { return u.re; }

    // regex builders
    expr_ref word(char const* s) { return expr_ref(re().mk_to_re(u.str.mk_string(zstring(s))), m); }
    expr_ref cat(expr* a, expr* b) { return expr_ref(re().mk_concat(a, b), m); }
    expr_ref alt(expr* a, expr* b) { return expr_ref(re().mk_union(a, b), m); }
    expr_ref star(expr* a) { return expr_ref(re().mk_star(a), m); }
    expr_ref inter(expr* a, expr* b) { return expr_ref(re().mk_inter(a, b), m); }
    expr_ref comp(expr* a) { return expr_ref(re().mk_complement(a), m); }
    expr_ref dot() { return expr_ref(re().mk_full_char(m_re), m); }
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
    char const* mode_name() const {
        switch (m_mode) {
        case seq_monadic::transition_mode::brzozowski: return "brz";
        case seq_monadic::transition_mode::light_antimirov: return "light-ant";
        }
        UNREACHABLE();
        return "";
    }

    bool eval_guard(expr* guard, unsigned ch) {
        sort* elem_sort = nullptr;
        VERIFY(u.is_seq(m_str, elem_sort));
        expr_ref v0(m.mk_var(0, elem_sort), m);
        expr_safe_replace rep(m);
        rep.insert(v0, u.str.mk_char(ch));
        expr_ref instantiated(m), simplified(m);
        rep(guard, instantiated);
        th_rewriter rw(m);
        rw(instantiated, simplified);
        return m.is_true(simplified);
    }

    void check_ant_cofactors() {
        expr_ref a = word("a");
        expr_ref any = dotstar();
        expr_ref dot3 = loop(dot(), 3, 3);
        expr_ref R = cat(any, cat(a, dot3));
        expr_ref_pair_vector cof(m);
        m_rw.light_ant_derivative_cofactors(R, cof);

        bool found_R = false, found_dot3 = false, ok = cof.size() == 2;
        for (auto const& [guard, target] : cof) {
            if (target == R) {
                found_R = eval_guard(guard, 'a') && eval_guard(guard, 'b');
            }
            else if (target == dot3) {
                found_dot3 = eval_guard(guard, 'a') && !eval_guard(guard, 'b');
            }
            else {
                ok = false;
            }
        }
        ok = ok && found_R && found_dot3;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ")
                  << mode_name() << " cofactor construction\n";
    }

    void check(char const* name, expr* term, expr* R, lbool expected) {
        m_mon.set_gen_model(false);               // this check does not use the model
        lbool got = m_mon.solve(term, R);
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    // assert the membership list: the primary (term in R) plus one (var in R') per extra
    // constraint, decided jointly by check().
    void add_extra(expr* term, expr* R, obj_map<expr, expr*> const& ve) {
        m_mon.add(term, R, nullptr);
        for (auto const& [k, v] : ve)
            m_mon.add(k, v, nullptr);
    }

    void check_extra(char const* name, expr* term, expr* R,
                     obj_map<expr, expr*> const& ve, lbool expected) {
        m_trail.push_scope();
        add_extra(term, R, ve);
        m_mon.set_gen_model(false);               // this check does not use the model
        lbool got = m_mon.check();
        m_trail.pop_scope(1);
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    // flatten a ground sequence term into its element values.
    void flatten_seq(expr* seqv, ptr_vector<expr>& elems) {
        zstring zs;
        if (u.str.is_concat(seqv)) {
            for (expr* arg : *to_app(seqv)) flatten_seq(arg, elems);
            return;
        }
        if (u.str.is_empty(seqv))
            return;
        if (u.str.is_string(seqv, zs)) {
            for (unsigned i = 0; i < zs.length(); ++i) elems.push_back(u.str.mk_char(zs, i));
            return;
        }
        if (u.str.is_unit(seqv))
            elems.push_back(to_app(seqv)->get_arg(0));
    }

    // decide membership of a concrete word (list of element values) in R by folding
    // derivatives and testing nullability of the residual.
    bool word_in_re(ptr_vector<expr> const& elems, expr* R) {
        expr_ref cur(R, m);
        for (expr* e : elems) cur = m_rw.mk_derivative(e, cur);
        return m.is_true(m_rw.is_nullable(cur));
    }

    // solve for a model, then check the returned witness assignment actually makes
    // term a member of R (substitute var -> witness and re-decide by derivatives).
    void check_witness(char const* name, expr* term, expr* R,
                       obj_map<expr, expr*> const& ve) {
        m_trail.push_scope();
        add_extra(term, R, ve);
        m_mon.set_gen_model(true);                // this check verifies the extracted model
        lbool got = m_mon.check();
        obj_map<expr, expr*> const& model = m_mon.get_model();
        bool ok = (got == l_true) && !model.empty();
        if (ok) {
            expr_safe_replace rep(m);
            for (auto const& kv : model) rep.insert(kv.m_key, kv.m_value);
            expr_ref g(m);
            rep(term, g);
            ptr_vector<expr> elems;
            flatten_seq(g, elems);
            ok = word_in_re(elems, R);
        }
        m_trail.pop_scope(1);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  solve=" << s(got) << " witness-verified=" << (ok ? "yes" : "no") << "\n";
    }

    // decide a conjunction of memberships jointly (shared variables constrained together).
    void check_and(char const* name, vector<std::pair<expr*, expr*>> const& mems, lbool expected) {
        m_trail.push_scope();
        for (auto const& [t, r] : mems)
            m_mon.add(t, r, nullptr);
        m_mon.set_gen_model(false);               // this check does not use the model
        lbool got = m_mon.check();
        m_trail.pop_scope(1);
        bool ok = (got == expected);
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

    // collect the core ids after a check() into `ids`.
    void core_ids(std::set<unsigned>& ids) {
        ids.clear();
        for (void* dep : m_mon.core()) {
            u_dependency* d = static_cast<u_dependency*>(dep);
            ids.insert(d->leaf_value());
        }
    }

    // Assert each membership with a distinct leaf dependency (id = its index) and expect
    // the conjunction to be UNSAT.  With minimization ON, core() must be exactly
    // `expected_core` (irrelevant constraints omitted); with minimization OFF, core()
    // must be all membership dependencies.
    void check_core(char const* name, vector<std::pair<expr*, expr*>> const& mems,
                    std::set<unsigned> const& expected_core) {
        m_mon.set_gen_model(false);
        std::set<unsigned> all_ids, got_ids;
        for (unsigned i = 0; i < mems.size(); ++i)
            all_ids.insert(i);

        // minimization disabled: the core is every asserted membership's dependency.
        m_mon.set_min_core(false);
        m_trail.push_scope();
        for (unsigned i = 0; i < mems.size(); ++i)
            m_mon.add(mems[i].first, mems[i].second, m_dm.mk_leaf(i));
        lbool got0 = m_mon.check();
        core_ids(got_ids);
        bool ok0 = (got0 == l_false) && (got_ids == all_ids);
        m_trail.pop_scope(1);

        // minimization enabled: the core drops constraints irrelevant to the conflict.
        m_mon.set_min_core(true);
        m_trail.push_scope();
        for (unsigned i = 0; i < mems.size(); ++i)
            m_mon.add(mems[i].first, mems[i].second, m_dm.mk_leaf(i));
        lbool got1 = m_mon.check();
        std::set<unsigned> min_ids;
        core_ids(min_ids);
        bool ok1 = (got1 == l_false) && (min_ids == expected_core);
        m_trail.pop_scope(1);
        m_mon.set_min_core(false);                // restore the harness default

        bool ok = ok0 && ok1;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name << "  got=" << s(got1) << " core={";
        bool first = true;
        for (unsigned id : min_ids) { std::cout << (first ? "" : ",") << id; first = false; }
        std::cout << "} full=" << (ok0 ? "yes" : "no") << "\n";
    }

    lbool smt_check(expr_ref_vector const& assertions, bool enable_monadic = true) {
        smt_params params;
        params.m_seq_regex_monadic = enable_monadic;
        smt::kernel solver(m, params);
        for (expr* assertion : assertions)
            solver.assert_expr(assertion);
        return solver.check();
    }

    void check_smt(char const* name, expr_ref_vector const& assertions, lbool expected,
                   bool enable_monadic = true) {
        lbool got = smt_check(assertions, enable_monadic);
        bool ok = got == expected;
        if (!ok) ++m_fail;
        std::cout << (ok ? "  OK   " : "  FAIL ") << name
                  << "  got=" << s(got) << " expected=" << s(expected) << "\n";
    }

public:
    seq_monadic_test(seq_monadic::transition_mode mode) :
        m_reg(m), m_rw(m), m_mon(m_rw, m_trail, mode), u(m), m_str(m), m_re(m), m_mode(mode) {
        m_str = u.str.mk_string_sort();
        m_re  = re().mk_re(m_str);
        m_mon.set_min_core(false);   // tests use unminimized cores by default
    }

    void run() {
        std::cout << "=== seq_monadic mode: " << mode_name() << " ===\n";
        if (m_mode == seq_monadic::transition_mode::light_antimirov)
            check_ant_cofactors();
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

        // ---- witness extraction: a produced witness must be a concrete SEQUENCE of
        // ---- elements that actually satisfies the membership (not a predicate).
        std::cout << "=== seq_monadic: witness extraction (char) ===\n";
        obj_map<expr, expr*> nove;
        check_witness("(a|b)*        x.a.x", xwx(x, "a"), star(alt(a, b)), nove);
        check_witness("Sig*aaSig*    x.a.x", xwx(x, "a"), saas, nove);      // forces nonempty x
        check_witness("~(a*.b)       x.a.x", xwx(x, "a"), comp(cat(star(a), b)), nove);
        check_witness("L3-03         x.a.x", xwx(x, "a"),
                      comp(cat(star(a), comp(cat(star(b), comp(star(ab)))))), nove);
        check_witness("(a|b)*        x.a.y", xay(x, y), star(alt(a, b)), nove);
        check_witness("Sig*          x.y.x", xyx(x, y), dotstar(), nove);
        check_witness("Sig* & y[0-9]+ x.a.y", xay(x, y), dotstar(), ve);    // ve: y in [0-9]+
        check_witness("[0-9]{2}&x[0-9]+ y[0-9]* x.y.x", xyx(x, y), loop22, ve2);

        // ---- generic element sort: sequences of Int exercise the non-character guard
        // ---- algebra (candidate-basis emptiness + witness), not seq::range_predicate.
        std::cout << "=== seq_monadic: generic element sort (Seq Int) ===\n";
        arith_util ar(m);
        sort_ref intS(ar.mk_int(), m);
        sort_ref seqI(u.str.mk_seq(intS), m);
        sort_ref reI(u.re.mk_re(seqI), m);
        expr_ref i1(ar.mk_numeral(rational(1), true), m);
        expr_ref i2(ar.mk_numeral(rational(2), true), m);
        expr_ref one_seq(u.str.mk_unit(i1), m);                 // [1] : (Seq Int)
        expr_ref re1(re().mk_to_re(u.str.mk_unit(i1)), m);      // matches [1]
        expr_ref re2(re().mk_to_re(u.str.mk_unit(i2)), m);      // matches [2]
        expr_ref re12s(star(alt(re1, re2)), m);                 // ([1]|[2])*
        expr_ref re2s(star(re2), m);                            // [2]*
        expr_ref xi(m.mk_const("xi", seqI), m);
        expr_ref yi(m.mk_const("yi", seqI), m);
        expr_ref xi1xi(sconcat(xi, sconcat(one_seq, xi)), m);   // xi.[1].xi
        expr_ref xiyi(sconcat(xi, sconcat(one_seq, yi)), m);    // xi.[1].yi
        obj_map<expr, expr*> nove2;
        check("([1]|[2])*   xi.[1].xi", xi1xi, re12s, l_true);
        check("[2]*         xi.[1].xi", xi1xi, re2s,  l_false); // the middle [1] is not in [2]*
        check("([1]|[2])*   xi        ", xi, re12s, l_true);
        check("([1]|[2])*   xi.[1].yi", xiyi, re12s, l_true);
        check_witness("([1]|[2])* xi.[1].xi", xi1xi, re12s, nove2);
        check_witness("([1]|[2])* xi       ", xi, re12s, nove2);
        check_witness("([1]|[2])* xi.[1].yi", xiyi, re12s, nove2);
        // per-variable extra constraint over (Seq Int): yi must also be in [2]*
        obj_map<expr, expr*> veI; veI.insert(yi, re2s.get());
        check_extra("([1]|[2])* & yi[2]* xi.[1].yi", xiyi, re12s, veI, l_true);
        check_witness("([1]|[2])* & yi[2]* xi.[1].yi", xiyi, re12s, veI);

        // ---- conjunction of memberships (add + check): a variable shared across memberships
        // ---- is constrained jointly.  These are cases that are individually SAT but
        // ---- jointly UNSAT -- exactly what independent per-membership solving gets wrong.
        std::cout << "=== seq_monadic: conjunction of memberships (add + check) ===\n";
        expr_ref aaS(star(cat(a, a)), m);           // (aa)*     : even number of a's
        expr_ref a_aaS(cat(a, star(cat(a, a))), m); // a(aa)*    : odd number of a's
        expr_ref abS(star(ab), m);                  // (ab)*
        expr_ref sig2(dotstar(), m);                // Sigma*
        // x in (aa)* /\ x in a(aa)*  : even-and-odd length of a's -> unsat (each alone sat)
        vector<std::pair<expr*, expr*>> mUnsat1;
        mUnsat1.push_back(std::make_pair((expr*)x.get(), (expr*)aaS.get()));
        mUnsat1.push_back(std::make_pair((expr*)x.get(), (expr*)a_aaS.get()));
        check_and("x in (aa)* & x in a(aa)*", mUnsat1, l_false);
        // compound terms sharing x: x.a in (aa)* (x odd) /\ x.aa in (aa)* (x even) -> unsat
        expr_ref tXa(sconcat(x, sword("a")), m);
        expr_ref tXaa(sconcat(x, sword("aa")), m);
        vector<std::pair<expr*, expr*>> mUnsat2;
        mUnsat2.push_back(std::make_pair((expr*)tXa.get(),  (expr*)aaS.get()));
        mUnsat2.push_back(std::make_pair((expr*)tXaa.get(), (expr*)aaS.get()));
        check_and("x.a in (aa)* & x.aa in (aa)*", mUnsat2, l_false);
        // consistent conjunction: x in (ab)* /\ x in Sigma*  -> sat (x=eps or ab)
        vector<std::pair<expr*, expr*>> mSat;
        mSat.push_back(std::make_pair((expr*)x.get(), (expr*)abS.get()));
        mSat.push_back(std::make_pair((expr*)x.get(), (expr*)sig2.get()));
        check_and("x in (ab)* & x in Sigma*", mSat, l_true);
        // two variables, two memberships: x.a.y in (a|b)* /\ y.b.x in (a|b)* -> sat
        expr_ref tXaY(xay(x, y), m);
        expr_ref tYbX(sconcat(y, sconcat(sword("b"), x)), m);
        expr_ref abStar(star(alt(a, b)), m);
        vector<std::pair<expr*, expr*>> mSat2;
        mSat2.push_back(std::make_pair((expr*)tXaY.get(), (expr*)abStar.get()));
        mSat2.push_back(std::make_pair((expr*)tYbX.get(), (expr*)abStar.get()));
        check_and("x.a.y & y.b.x in (a|b)*", mSat2, l_true);

        std::cout << "=== seq_monadic: assertion trail ===\n";
        m_mon.set_gen_model(false);
        m_trail.push_scope();
        m_mon.add(x, aaS, nullptr);
        lbool before = m_mon.check();
        m_trail.push_scope();
        m_mon.add(x, a_aaS, nullptr);
        lbool with_conflict = m_mon.check();
        lbool repeated = m_mon.check();
        m_trail.pop_scope(1);
        lbool after_pop = m_mon.check();
        m_trail.pop_scope(1);
        lbool empty = m_mon.check();
        bool trail_ok = before == l_true && with_conflict == l_false &&
                        repeated == l_false && after_pop == l_true && empty == l_true;
        if (!trail_ok) ++m_fail;
        std::cout << (trail_ok ? "  OK   " : "  FAIL ")
                  << "check preserves assertions and pop removes them\n";

        std::cout << "=== seq_monadic: length bounds ===\n";
        auto check_bound = [&](char const* name, expr* regex, unsigned bound, bool is_lo,
                               lbool expected) {
            m_trail.push_scope();
            m_mon.add(x, regex, nullptr);
            if (is_lo)
                m_mon.add_lo(x, bound, nullptr);
            else
                m_mon.add_hi(x, bound, nullptr);
            lbool got = m_mon.check();
            m_trail.pop_scope(1);
            bool ok = got == expected;
            if (!ok) ++m_fail;
            std::cout << (ok ? "  OK   " : "  FAIL ") << name
                      << "  got=" << s(got) << " expected=" << s(expected) << "\n";
        };
        check_bound("x in a, |x| >= 1", word("a"), 1, true, l_true);
        check_bound("x in a, |x| >= 2", word("a"), 2, true, l_false);
        check_bound("x in aa, |x| <= 2", word("aa"), 2, false, l_true);
        check_bound("x in aa, |x| <= 1", word("aa"), 1, false, l_false);
        check_bound("x in epsilon, |x| <= 0", word(""), 0, false, l_true);
        auto check_len = [&](char const* name, expr* regex, unsigned len, lbool expected) {
            m_trail.push_scope();
            m_mon.add(x, regex, nullptr);
            m_mon.add_len(x, len, nullptr);
            lbool got = m_mon.check();
            m_trail.pop_scope(1);
            bool ok = got == expected;
            if (!ok) ++m_fail;
            std::cout << (ok ? "  OK   " : "  FAIL ") << name
                      << "  got=" << s(got) << " expected=" << s(expected) << "\n";
        };
        check_len("x in aa, |x| = 2", word("aa"), 2, l_true);
        check_len("x in aa, |x| = 1", word("aa"), 1, l_false);
        check_len("x in epsilon, |x| = 0", word(""), 0, l_true);
        m_trail.push_scope();
        unsigned trail_size = m_trail.size();
        m_mon.add_lo(x, 0, m_dm.mk_leaf(0));
        bool zero_lo_ok = m_trail.size() == trail_size && m_mon.check() == l_true;
        m_trail.pop_scope(1);
        if (!zero_lo_ok) ++m_fail;
        std::cout << (zero_lo_ok ? "  OK   " : "  FAIL ")
                  << "|x| >= 0 is a no-op\n";

        // Length bounds on COMPOUND terms and on several variables at once: the shape the
        // SMT-LIB regex benchmarks use (e.g. `x.y.x in R /\ |x|>0 /\ |y|>0`).  A bound on
        // a concatenation constrains the term as a whole; bounds on the individual
        // variables have to be intersected with the split induced by the membership.
        std::cout << "=== seq_monadic: length bounds on compound terms ===\n";
        auto check_bounded = [&](char const* name,
                                 auto&& assert_all, lbool expected) {
            m_trail.push_scope();
            assert_all();
            lbool got = m_mon.check();
            m_trail.pop_scope(1);
            bool ok = got == expected;
            if (!ok) ++m_fail;
            std::cout << (ok ? "  OK   " : "  FAIL ") << name
                      << "  got=" << s(got) << " expected=" << s(expected) << "\n";
        };
        expr_ref t_xyx(xyx(x, y), m);
        expr_ref t_xax(xwx(x, "a"), m);
        // |x.y.x| is odd-free: x.y.x in (ab)* with |x.y.x| = 2 forces x.y.x = "ab"
        check_bounded("x.y.x in (ab)*, |x.y.x| = 2", [&] {
            m_mon.add(t_xyx, abS, nullptr);
            m_mon.add_len(t_xyx, 2, nullptr);
        }, l_true);
        check_bounded("x.y.x in (ab)*, |x.y.x| = 3", [&] {
            m_mon.add(t_xyx, abS, nullptr);
            m_mon.add_len(t_xyx, 3, nullptr);      // (ab)* has only even lengths
        }, l_false);
        // bounds on the individual variables of a compound membership
        check_bounded("x.a.x in Sigma*, |x| >= 2, |x.a.x| <= 5", [&] {
            m_mon.add(t_xax, sig2, nullptr);
            m_mon.add_lo(x, 2, nullptr);
            m_mon.add_hi(t_xax, 5, nullptr);
        }, l_true);
        check_bounded("x.a.x in Sigma*, |x| >= 3, |x.a.x| <= 5", [&] {
            m_mon.add(t_xax, sig2, nullptr);
            m_mon.add_lo(x, 3, nullptr);           // |x.a.x| = 2|x|+1 >= 7 > 5
            m_mon.add_hi(t_xax, 5, nullptr);
        }, l_false);
        // two variables bounded independently under one membership
        check_bounded("x.y.x in (a|b)*, |x| = 1, |y| = 2", [&] {
            m_mon.add(t_xyx, abStar, nullptr);
            m_mon.add_len(x, 1, nullptr);
            m_mon.add_len(y, 2, nullptr);
        }, l_true);
        check_bounded("x.y.x in a*, |x| >= 1, y in b*", [&] {
            m_mon.add(t_xyx, star(a), nullptr);
            m_mon.add(y, star(b), nullptr);        // y must be both a* and b* -> y = eps
            m_mon.add_lo(x, 1, nullptr);
            m_mon.add_lo(y, 1, nullptr);           // ... but |y| >= 1
        }, l_false);
        // the bound is the ONLY reason for unsat: without it the membership is satisfiable
        check_bounded("x in a(aa)* (no bound)", [&] {
            m_mon.add(x, a_aaS, nullptr);
        }, l_true);
        check_bounded("x in a(aa)*, |x| = 2", [&] {
            m_mon.add(x, a_aaS, nullptr);          // only odd lengths
            m_mon.add_len(x, 2, nullptr);
        }, l_false);
        // upper and lower bounds that cross
        check_bounded("x in Sigma*, |x| >= 3, |x| <= 2", [&] {
            m_mon.add(x, sig2, nullptr);
            m_mon.add_lo(x, 3, nullptr);
            m_mon.add_hi(x, 2, nullptr);
        }, l_false);

        // The IPv6 abbreviation benchmark shape: an intersection of a positive "contains"
        // and a complement, restricted to a character range, over  x.y.x  with both
        // variables non-empty.  Without the length bounds the answer is trivially sat via
        // x = y = epsilon, so the bounds are what make the test meaningful.
        {
            expr_ref cc(word("::"), m);
            expr_ref sig_plus(cat(dot(), dotstar()), m);
            expr_ref has_cc(cat(dotstar(), cat(cc, dotstar())), m);
            expr_ref two_cc(cat(dotstar(), cat(cc, cat(sig_plus, cat(cc, dotstar())))), m);
            expr_ref hexcol(star(alt(rng('0', '9'),
                                 alt(rng('A', 'F'),
                                 alt(rng('a', 'f'), word(":"))))), m);
            expr_ref R6(inter(has_cc, inter(comp(two_cc), hexcol)), m);
            check_bounded("ipv6: x.y.x in R, |x|>=1, |y|>=1", [&] {
                m_mon.add(t_xyx, R6, nullptr);
                m_mon.add_lo(x, 1, nullptr);
                m_mon.add_lo(y, 1, nullptr);
            }, l_true);
            // "::" cannot be split across a repeated x without creating a second group,
            // and hexcol forbids everything outside [0-9A-Fa-f:], so a long x is hopeless
            check_bounded("ipv6: x.y.x in R, |x|>=1, |y|>=1, |x.y.x|<=2", [&] {
                m_mon.add(t_xyx, R6, nullptr);
                m_mon.add_lo(x, 1, nullptr);
                m_mon.add_lo(y, 1, nullptr);
                m_mon.add_hi(t_xyx, 2, nullptr);   // needs >= 3 chars to hold "::" plus x twice
            }, l_false);
        }

        std::cout << "=== seq_monadic: SMT regex end-game ===\n";
        {
            expr_ref_vector assertions(m);
            assertions.push_back(re().mk_in_re(x, star(alt(a, b))));
            check_smt("enabled SAT membership", assertions, l_true);
            check_smt("disabled legacy membership", assertions, l_true, false);
        }
        {
            expr_ref_vector assertions(m);
            expr_ref a_star(star(a), m);
            assertions.push_back(re().mk_in_re(x, a_star));
            assertions.push_back(re().mk_in_re(x, comp(a_star)));
            check_smt("enabled joint UNSAT memberships", assertions, l_false);
        }
        {
            expr_ref_vector assertions(m);
            assertions.push_back(m.mk_not(re().mk_in_re(x, star(a))));
            assertions.push_back(re().mk_in_re(x, star(a)));
            check_smt("enabled negative membership", assertions, l_false);
        }
        {
            expr_ref_vector assertions(m);
            assertions.push_back(m.mk_eq(x, sword("aa")));
            assertions.push_back(re().mk_in_re(x, expr_ref(re().mk_plus(a), m)));
            check_smt("rejected witness uses legacy fallback", assertions, l_true);
        }
        {
            expr_ref_vector assertions(m);
            assertions.push_back(m.mk_eq(x, y));
            assertions.push_back(re().mk_in_re(x, star(a)));
            assertions.push_back(re().mk_in_re(y, expr_ref(re().mk_plus(b), m)));
            check_smt("aliased variables use legacy fallback", assertions, l_false);
        }
        {
            arith_util ar2(m);
            sort_ref int_sort(ar2.mk_int(), m);
            sort_ref seq_sort(u.str.mk_seq(int_sort), m);
            sort_ref regex_sort(re().mk_re(seq_sort), m);
            expr_ref seq_var(m.mk_const("seq_var", seq_sort), m);
            expr_ref elem_var(m.mk_const("elem_var", int_sort), m);
            expr_ref symbolic_unit(u.str.mk_unit(elem_var), m);
            expr_ref term(u.str.mk_concat(seq_var, symbolic_unit), m);
            expr_ref_vector assertions(m);
            assertions.push_back(re().mk_in_re(term, re().mk_full_seq(regex_sort)));
            check_smt("unsupported symbolic unit uses fallback", assertions, l_true);
        }
        {
            smt_params params;
            params.m_seq_regex_monadic = true;
            smt::kernel solver(m, params);
            expr_ref a_star(star(a), m);
            solver.assert_expr(re().mk_in_re(x, a_star));
            lbool before_push = solver.check();
            solver.push();
            solver.assert_expr(re().mk_in_re(x, comp(a_star)));
            lbool in_push = solver.check();
            solver.pop(1);
            lbool after_pop = solver.check();
            bool ok = before_push == l_true && in_push == l_false && after_pop == l_true;
            if (!ok) ++m_fail;
            std::cout << (ok ? "  OK   " : "  FAIL ")
                      << "SMT membership trail push/pop\n";
        }

        // ---- unsat cores: the extracted core must contain only constraints that
        // ---- participate in the contradiction, not independent ones.
        std::cout << "=== seq_monadic: unsat cores ===\n";
        // x in a* /\ x in ~(a*) /\ y in b*  -> unsat over x; core = {0,1}, not the y-constraint.
        {
            expr_ref aStar(star(a), m), naStar(comp(star(a)), m), bStar(star(b), m);
            vector<std::pair<expr*, expr*>> ms;
            ms.push_back(std::make_pair((expr*)x.get(), (expr*)aStar.get()));
            ms.push_back(std::make_pair((expr*)x.get(), (expr*)naStar.get()));
            ms.push_back(std::make_pair((expr*)y.get(), (expr*)bStar.get()));
            check_core("x in a* & x in ~a* (& y in b*)", ms, std::set<unsigned>{0, 1});
        }
        // x in (aa)* /\ x in a(aa)* /\ y in Sigma*  -> unsat over x; core = {0,1}.
        {
            expr_ref aaS(star(cat(a, a)), m), a_aaS(cat(a, star(cat(a, a))), m), sigStar(dotstar(), m);
            vector<std::pair<expr*, expr*>> ms;
            ms.push_back(std::make_pair((expr*)x.get(),  (expr*)aaS.get()));
            ms.push_back(std::make_pair((expr*)x.get(),  (expr*)a_aaS.get()));
            ms.push_back(std::make_pair((expr*)y.get(),  (expr*)sigStar.get()));
            check_core("x in (aa)* & x in a(aa)* (& y in Sig*)", ms, std::set<unsigned>{0, 1});
        }
        // Three independent constraints, contradiction only between the middle two:
        // z in a* (indep) /\ x in b* /\ x in a+ (x=empty allowed by b*, a+ forbids empty)
        {
            expr_ref z = var("z");
            expr_ref aStarZ(star(a), m), bStarX(star(b), m), aP(cat(a, star(a)), m);   // a+ = at least one a
            vector<std::pair<expr*, expr*>> ms;
            ms.push_back(std::make_pair((expr*)z.get(), (expr*)aStarZ.get()));    // 0: irrelevant
            ms.push_back(std::make_pair((expr*)x.get(), (expr*)bStarX.get()));    // 1: x in b*
            ms.push_back(std::make_pair((expr*)x.get(), (expr*)aP.get()));        // 2: x in a+
            check_core("z in a* (& x in b* & x in a+)", ms, std::set<unsigned>{1, 2});
        }

        std::cout << "=== seq_monadic: " << (m_fail == 0 ? "ALL PASS" : "FAILURES") << " ("
                  << m_fail << " fail) ===\n";
        ENSURE(m_fail == 0);
    }
};

}

void tst_seq_monadic() {
    seq_monadic_test brz(seq_monadic::transition_mode::brzozowski);
    brz.run();
    seq_monadic_test light_ant(seq_monadic::transition_mode::light_antimirov);
    light_ant.run();
}
