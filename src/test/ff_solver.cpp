/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_solver.cpp

Abstract:

    Frontend-independent finite-field reasoning tests. These exercise the
    reusable interface directly, without a smt::context or SAT solver.

--*/
#include "ast/ff/ff_solver.h"
#include "ast/reg_decl_plugins.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "util/debug.h"
#include "util/z3_exception.h"
#include "tactic/ff/ff_solve_tactic.h"
#include "tactic/tactic.h"

namespace {
    // Test-only convenience wrapper: assigns each add() call a dependency
    // leaf encoding its chronological index as a void* key, and tracks the
    // literal premise expression so tests can translate a returned conflict
    // core back to formulas and indices.
    class test_problem {
        ast_manager &m;
        ff::solver core_;
        expr_ref_vector premises_;
    public:
        test_problem(ast_manager &m, sort *s, params_ref const &p,
                     ff::ff_encoding_cache *cache = nullptr, ff::basis_cache *basis = nullptr)
            : m(m), core_(m, s, p, cache, basis), premises_(m) {}
        void add(expr *a, expr *b, bool equality) {
            expr_ref premise(m.mk_eq(a, b), m);
            if (!equality) premise = m.mk_not(premise);
            v_dependency *d = core_.dep_manager().mk_leaf(reinterpret_cast<void *>(static_cast<uintptr_t>(premises_.size())));
            core_.add(a, b, equality, d);
            premises_.push_back(premise);
        }
        lbool check() { return core_.check(); }
        rational value(expr *term) { return core_.value(term); }
        expr *premise(unsigned index) const { return premises_.get(index); }
        std::set<unsigned> conflict() const {
            vector<void *, false> ptrs;
            core_.dep_manager().linearize(core_.conflict(), ptrs);
            std::set<unsigned> result;
            for (void *ptr : ptrs)
                result.insert(static_cast<unsigned>(reinterpret_cast<uintptr_t>(ptr)));
            return result;
        }
        void collect_statistics(statistics &st) const { core_.collect_statistics(st); }
        bool encoding_limit_hit() const { return core_.encoding_limit_hit(); }
        unsigned encoding_steps() const { return core_.encoding_steps(); }
    };

    bool holds(ast_manager &m, expr *formula, expr *x, expr *y, unsigned a, unsigned b) {
        ff_util ff(m);
        expr_safe_replace subst(m);
        expr_ref ax(ff.mk_numeral(rational(a), x->get_sort()), m);
        expr_ref by(ff.mk_numeral(rational(b), y->get_sort()), m);
        subst.insert(x, ax);
        subst.insert(y, by);
        expr_ref value(formula, m);
        subst(value);
        th_rewriter rw(m);
        rw(value);
        ENSURE(m.is_true(value) || m.is_false(value));
        return m.is_true(value);
    }

    void exhaustive_problems() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        unsigned checked = 0;
        for (unsigned prime : {2u, 3u, 7u}) {
            sort_ref field(ff.mk_sort(rational(prime)), m);
            expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
            expr_ref product(ff.mk_mul(x, y), m), sum(ff.mk_add(x, y), m);
            ff::ff_encoding_cache cache(m, field);
            ff::basis_cache basis;
            // Reuse pure encodings while changing all input equations. Test
            // compact encodings too: their fresh definitions must stay local.
            for (bool preprocess : {false, true})
              for (bool compact : {false, true})
                for (unsigned a = 0; a < prime; ++a)
                    for (unsigned b = 0; b < prime; ++b) {
                        params_ref params;
                        params.set_bool("ff.compact_encoding", compact);
                        params.set_bool("solve_eqs", preprocess);
                        test_problem core(m, field, params, &cache, &basis);
                        expr_ref ca(ff.mk_numeral(rational(a), field), m);
                        expr_ref cb(ff.mk_numeral(rational(b), field), m);
                        core.add(product, ca, true);
                        core.add(sum, cb, true);
                        core.add(x, cb, false);
                        bool exists = false;
                        for (unsigned u = 0; u < prime; ++u)
                            for (unsigned v = 0; v < prime; ++v)
                                exists |= u*v % prime == a && (u+v) % prime == b && u != b;
                        lbool result = core.check();
                        ENSURE(result == (exists ? l_true : l_false));
                        if (exists) {
                            rational u = core.value(x), v = core.value(y);
                            ENSURE(mod(u*v, rational(prime)) == rational(a));
                            ENSURE(mod(u+v, rational(prime)) == rational(b));
                            ENSURE(u != rational(b));
                        }
                        else {
                            // Check only the reported supporting premises by
                            // exhaustive enumeration, independently of algebra.
                            for (unsigned u = 0; u < prime; ++u)
                                for (unsigned v = 0; v < prime; ++v) {
                                    bool witness = true;
                                    for (unsigned index : core.conflict()) {
                                        ENSURE(index < 3);
                                        witness &= holds(m, core.premise(index), x, y, u, v);
                                    }
                                    ENSURE(!witness);
                                }
                        }
                        ++checked;
                    }
            ENSURE(cache.size() > 0);
            cache.reset();
            ENSURE(cache.size() == 0);
        }
        ENSURE(checked == 248);
    }

    void interface_and_scope_contract() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref field(ff.mk_sort(rational(7)), m), other(ff.mk_sort(rational(11)), m);
        expr_ref x(m.mk_const("x", field), m), y(m.mk_const("y", field), m);
        expr_ref z(m.mk_const("z", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m), one(ff.mk_numeral(rational(1), field), m);
        expr_ref square(ff.mk_mul(x, x), m);
        ff::ff_encoding_cache cache(m, field);
        ff::basis_cache basis;
        params_ref params;
        {
            test_problem core(m, field, params, &cache, &basis);
            core.add(y, square, true);
            core.add(z, ff.mk_add(y, one), true);
            core.add(x, zero, true);
            core.add(z, one, false);
            ENSURE(core.check() == l_false);
            // All four premises are necessary in F7; no scope-local definition
            // may disappear from the explanation of the contradiction.
            ENSURE(core.conflict().size() == 4);
        }
        {
            test_problem core(m, field, params, &cache, &basis);
            core.add(z, zero, true);
            ENSURE(core.check() == l_true && core.value(z).is_zero());
            bool rejected = false;
            try { core.add(z, one, true); }
            catch (default_exception const &) { rejected = true; }
            ENSURE(rejected);
        }
        bool rejected = false;
        try { test_problem wrong(m, other, params, &cache); }
        catch (default_exception const &) { rejected = true; }
        ENSURE(rejected);
        // Foreign terms are opaque field leaves, including non-field arguments.
        // A mock frontend supplies their congruence equality as an explicit fact.
        sort* domain[] = {m.mk_bool_sort()};
        func_decl_ref f(m.mk_func_decl(symbol("f"), 1, domain, field), m);
        expr_ref a(m.mk_app(f, m.mk_true()), m), b(m.mk_app(f, m.mk_false()), m);
        {
            test_problem core(m, field, params, &cache);
            core.add(a, zero, true); core.add(b, one, true);
            ENSURE(core.check() == l_true);
            ENSURE(core.value(a).is_zero() && core.value(b).is_one());
        }
        {
            test_problem core(m, field, params, &cache);
            core.add(a, zero, true); core.add(b, one, true); core.add(a, b, true);
            ENSURE(core.check() == l_false);
            ENSURE(core.conflict().size() == 3);
        }
        // A canceled check exposes no candidate; a fresh problem can reuse the
        // pure cache after cancellation is reset, without any stale assertions.
        {
            test_problem core(m, field, params, &cache);
            core.add(x, zero, true);
            m.limit().inc_cancel();
            try { core.check(); } catch (ff::exhausted const &) {}
            m.limit().dec_cancel();
            bool unavailable = false;
            try { core.value(x); } catch (default_exception const &) { unavailable = true; }
            ENSURE(unavailable);
        }
        test_problem recovered(m, field, params, &cache);
        recovered.add(x, one, true);
        ENSURE(recovered.check() == l_true && recovered.value(x).is_one());
    }

    void preprocessing_contract() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref field(ff.mk_sort(rational(7)), m);
        expr_ref x(m.mk_const("px", field), m), y(m.mk_const("py", field), m);
        expr_ref z(m.mk_const("pz", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m);
        expr_ref one(ff.mk_numeral(rational(1), field), m);
        expr_ref two(ff.mk_numeral(rational(2), field), m);
        ff::ff_encoding_cache cache(m, field);
        params_ref params, no_algebra;
        no_algebra.set_uint("ff.max_steps", 0);
        {
            // Generic solve-eqs must discharge this without invoking algebra.
            // Using the input formulas themselves as dependency labels freezes
            // x and y and prevents the required substitutions.
            test_problem core(m, field, no_algebra, &cache);
            core.add(x, zero, true);
            core.add(y, ff.mk_add(x, one), true);
            core.add(y, one, false);
            core.add(z, two, true);
            ENSURE(core.check() == l_false);
            ENSURE(core.conflict() == std::set<unsigned>({0, 1, 2}));
        }
        expr_ref c(m.mk_const("pc", m.mk_bool_sort()), m);
        expr_ref leaf(m.mk_ite(c, x, zero), m);
        for (unsigned value = 0; value < 7; ++value) {
            // Only pure encodings survive. New assignments reconstruct fresh
            // values for eliminated variables and the same opaque ITE leaf.
            test_problem core(m, field, params, &cache);
            expr_ref n(ff.mk_numeral(rational(value), field), m);
            core.add(x, n, true);
            core.add(y, ff.mk_add(ff.mk_mul(x, x), one), true);
            core.add(leaf, y, true);
            ENSURE(core.check() == l_true);
            ENSURE(core.value(x) == rational(value));
            ENSURE(core.value(y) == rational((value * value + 1) % 7));
            ENSURE(core.value(leaf) == core.value(y));
        }
        {
            // The field solver treats a foreign term as opaque; it must not
            // substitute inside the ITE and silently change its identity.
            test_problem core(m, field, params, &cache);
            core.add(x, zero, true);
            core.add(leaf, one, true);
            ENSURE(core.check() == l_true && core.value(leaf).is_one());
            // The frontend's selected-branch equality rules out this candidate.
            test_problem combined(m, field, params, &cache);
            combined.add(x, zero, true);
            combined.add(leaf, one, true);
            combined.add(leaf, x, true);
            ENSURE(combined.check() == l_false);
            ENSURE(combined.conflict().size() == 3);
        }
        {
            // Inconsistent cyclic definitions cannot be eliminated together.
            test_problem core(m, field, params, &cache);
            core.add(x, ff.mk_add(y, one), true);
            core.add(y, ff.mk_add(x, one), true);
            ENSURE(core.check() == l_false);
            ENSURE(core.conflict().size() == 2);
        }
    }

    void bit_domain_preservation() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref field(ff.mk_sort(rational(257)), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m);
        expr_ref one(ff.mk_numeral(rational(1), field), m);
        params_ref params;
        params.set_uint("ff.max_steps", 1000);
        for (bool factored : {false, true}) {
            test_problem core(m, field, params);
            expr_ref_vector xs(m), ys(m), left(m), right(m);
            for (unsigned i = 0; i < 4; ++i) {
                expr_ref x(m.mk_fresh_const("bit.x", field), m);
                expr_ref y(m.mk_fresh_const("bit.y", field), m);
                xs.push_back(x); ys.push_back(y);
                for (expr *v : {x.get(), y.get()}) {
                    if (factored)
                        core.add(ff.mk_mul(v, ff.mk_add(v, ff.mk_neg(one))), zero, true);
                    else
                        core.add(ff.mk_mul(v, v), v, true);
                }
                expr_ref weight(ff.mk_numeral(rational(1u << i), field), m);
                left.push_back(ff.mk_mul(weight, x));
                right.push_back(ff.mk_mul(weight, y));
            }
            // Equal four-bit packs over F257 have identical bits: both integer
            // sums lie in [0,15], below the modulus. Eliminating a bit through
            // the pack equation obscures its domain and defeats bit propagation.
            core.add(ff.mk_add(left), ff.mk_add(right), true);
            core.add(xs.get(0), ys.get(0), false);
            ENSURE(core.check() == l_false);
        }
        {
            // The domain detector may match a polynomial identity. Preservation
            // must never turn that heuristic match into a Boolean assumption.
            test_problem core(m, field, params);
            expr_ref x(m.mk_const("not.a.bit", field), m);
            expr_ref square(ff.mk_mul(x, x), m);
            expr_ref two(ff.mk_numeral(rational(2), field), m);
            core.add(square, square, true);
            core.add(x, two, true);
            ENSURE(core.check() == l_true && core.value(x) == rational(2));
        }
    }

    void tactic_dependencies() {
        ast_manager m;
        reg_decl_plugins(m);
        ff_util ff(m);
        sort_ref field(ff.mk_sort(rational(7)), m);
        expr_ref x(m.mk_const("tx", field), m), y(m.mk_const("ty", field), m);
        expr_ref z(m.mk_const("tz", field), m);
        expr_ref zero(ff.mk_numeral(rational(0), field), m);
        expr_ref one(ff.mk_numeral(rational(1), field), m);
        expr_ref two(ff.mk_numeral(rational(2), field), m);
        expr_ref_vector formulas(m), labels(m);
        formulas.push_back(m.mk_eq(x, zero));
        formulas.push_back(m.mk_eq(y, ff.mk_add(x, one)));
        formulas.push_back(m.mk_not(m.mk_eq(y, one)));
        formulas.push_back(m.mk_eq(z, two));
        goal_ref g = alloc(goal, m, true, false, true);
        for (expr *f : formulas) {
            labels.push_back(m.mk_fresh_const("support", m.mk_bool_sort()));
            g->assert_expr(f, nullptr, m.mk_leaf(labels.back()));
        }
        params_ref params;
        params.set_uint("ff.enum_bits", 0);
        tactic_ref solve = mk_ff_solve_tactic(m, params);
        goal_ref_buffer result;
        (*solve)(g, result);
        ENSURE(result.size() == 1 && result[0]->inconsistent());
        ptr_vector<expr> support;
        m.linearize(result[0]->dep(0), support);
        ENSURE(support.size() == 3);
        for (unsigned i = 0; i < 3; ++i)
            ENSURE(support.contains(labels.get(i)));
        ENSURE(!support.contains(labels.get(3)));
    }

}

void tst_ff_solver() {
    exhaustive_problems();
    interface_and_scope_contract();
    preprocessing_contract();
    bit_domain_preservation();
    tactic_dependencies();
}
