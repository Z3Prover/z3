/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    tactic_scope.cpp

Abstract:

    scope_tactic routes the keys <path>.<key> of the tactic module to the step it
    names, locally and globally, with the precedence: forced author value, local
    scoped, local unscoped, global scoped, global unscoped, author default. Nested
    scopes are more specific. <path>.enabled false skips the step.

--*/
#include <memory>
#include <sstream>
#include "ast/reg_decl_plugins.h"
#include "tactic/goal.h"
#include "tactic/tactical.h"
#include "util/gparams.h"
#include "util/debug.h"

// Keys for the scopes of the test pipeline. Global scoped keys need a row in the
// tactic module; local keys are validated against the descriptors of the pipeline.
#define TEST_SCOPE_PARAMS(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_) \
  BOOL_(flat,          "test_scope.flat",          true, "test key") \
  BOOL_(inner_flat,    "test_scope.inner.flat",    true, "test key") \
  BOOL_(inner_enabled, "test_scope.inner.enabled", true, "test key")
Z3_DEFINE_MODULE_PARAMS(test_scope_params, "tactic", TEST_SCOPE_PARAMS, nullptr);
#undef TEST_SCOPE_PARAMS

namespace {

    // Resets all global parameters on exit.
    struct gparams_reset {
        ~gparams_reset() { gparams::reset(); }
    };

    // A step that keeps the parameters of its last updt_params and counts its runs.
    // It reads "flat" as the rewriter does: local value, else the global
    // rewriter.flat if the local one is a default, else false.
    class record_tactic : public tactic {
    public:
        // params_ref::reset would clear the entries it shares with the caller
        std::unique_ptr<params_ref> m_p = std::make_unique<params_ref>();
        unsigned   m_runs = 0;
        void updt_params(params_ref const & p) override { m_p = std::make_unique<params_ref>(p); }
        void collect_param_descrs(param_descrs & r) override {
            r.insert("flat", CPK_BOOL, "test key", "false", "rewriter");
        }
        void operator()(goal_ref const & in, goal_ref_buffer & result) override {
            ++m_runs;
            result.push_back(in.get());
        }
        void cleanup() override {}
        tactic * translate(ast_manager &) override { return alloc(record_tactic); }
        char const * name() const override { return "record"; }
        bool flat() const { return m_p->get_bool("flat", gparams::get_module("rewriter"), false); }
    };

    // scope test_scope
    //   a: author default flat=true
    //   scope test_scope.inner
    //     b: author default flat=true
    //   scope test_scope.inner
    //     c: author forced flat=true
    struct pipeline {
        record_tactic * a, * b, * c;
        tactic_ref t;
        pipeline() : a(alloc(record_tactic)), b(alloc(record_tactic)), c(alloc(record_tactic)) {
            params_ref dflt, forced;
            dflt.set_default_bool("flat", true);
            forced.set_bool("flat", true);
            t = scope_tactic("test_scope",
                             and_then(using_params(a, dflt),
                                      scope_tactic("test_scope.inner", using_params(b, dflt)),
                                      scope_tactic("test_scope.inner", using_params(c, forced))));
        }
        // the flat of a, b and c after updt_params(p), as "TFT"
        std::string flats(params_ref const & p) {
            t->updt_params(p);
            std::string r;
            for (record_tactic * s : { a, b, c })
                r += s->flat() ? "T" : "F";
            return r;
        }
        // the runs of a, b and c when applied after updt_params(p), as "110"
        std::string runs(params_ref const & p) {
            t->updt_params(p);
            ast_manager m;
            reg_decl_plugins(m);
            goal_ref g = alloc(goal, m);
            g->assert_expr(m.mk_const("q", m.mk_bool_sort()));
            goal_ref_buffer result;
            unsigned a0 = a->m_runs, b0 = b->m_runs, c0 = c->m_runs;
            (*t)(g, result);
            t->cleanup();
            ENSURE(result.size() == 1 && result[0]->size() == 1);
            return std::to_string(a->m_runs - a0) + std::to_string(b->m_runs - b0) + std::to_string(c->m_runs - c0);
        }
    };

    params_ref mk(std::initializer_list<std::pair<char const *, bool>> kvs) {
        params_ref p;
        for (auto const & [k, v] : kvs)
            p.set_bool(k, v);
        return p;
    }

    std::string flats(params_ref const & p) {
        pipeline pl;
        return pl.flats(p);
    }

    std::string runs(params_ref const & p) {
        pipeline pl;
        return pl.runs(p);
    }
}

#define ENSURE_EQ(a, b) { auto _a = (a); auto _b = (b); if (_a != _b) std::cerr << __LINE__ << ": " << _a << " != " << _b << "\n"; ENSURE(_a == _b); }

static void tst_local() {
    ENSURE_EQ(flats(params_ref()), "TTT");
    // a scoped key reaches the steps in the scope; forced values win
    ENSURE_EQ(flats(mk({{"test_scope.flat", false}})), "FFT");
    ENSURE_EQ(flats(mk({{"tactic.test_scope.flat", false}})), "FFT");
    ENSURE_EQ(flats(mk({{"test_scope.inner.flat", false}})), "TFT");
    // the more specific scope wins
    ENSURE_EQ(flats(mk({{"test_scope.flat", false}, {"test_scope.inner.flat", true}})), "FTT");
    ENSURE_EQ(flats(mk({{"test_scope.inner.flat", true}, {"test_scope.flat", false}})), "FTT");
    // local scoped beats local unscoped
    ENSURE_EQ(flats(mk({{"flat", false}, {"test_scope.inner.flat", true}})), "FTT");
    ENSURE_EQ(flats(mk({{"flat", true}, {"test_scope.inner.flat", false}})), "TFT");
    // a later updt_params replaces the scoped values
    pipeline pl;
    ENSURE_EQ(pl.flats(mk({{"test_scope.flat", false}})), "FFT");
    ENSURE_EQ(pl.flats(params_ref()), "TTT");
}

static void tst_global() {
    gparams_reset _r;
    {
        gparams_reset r;
        // global unscoped beats an author default, as before
        gparams::set("rewriter.flat", "false");
        ENSURE_EQ(flats(params_ref()), "FFT");
        // global scoped beats global unscoped
        gparams::set("tactic.test_scope.inner.flat", "true");
        ENSURE_EQ(flats(params_ref()), "FTT");
    }
    {
        gparams_reset r;
        gparams::set("tactic.test_scope.inner.flat", "false");
        ENSURE_EQ(flats(params_ref()), "TFT");
        // local unscoped beats global scoped
        ENSURE_EQ(flats(mk({{"flat", true}})), "TTT");
        // local scoped beats global scoped
        ENSURE_EQ(flats(mk({{"test_scope.inner.flat", true}})), "TTT");
        // a local key of an enclosing scope beats a global key of an inner scope
        ENSURE_EQ(flats(mk({{"test_scope.flat", true}})), "TTT");
    }
    {
        gparams_reset r;
        // nested global scopes: the more specific wins, though the enclosing scope
        // already set flat for the inner one
        gparams::set("tactic.test_scope.flat", "false");
        ENSURE_EQ(flats(params_ref()), "FFT");
        gparams::set("tactic.test_scope.inner.flat", "true");
        ENSURE_EQ(flats(params_ref()), "FTT");
        // a local key of the inner scope beats a global key of the enclosing one
        gparams::reset();
        gparams::set("tactic.test_scope.flat", "false");
        ENSURE_EQ(flats(mk({{"test_scope.inner.flat", true}})), "FTT");
    }
    {
        gparams_reset r;
        // a global key set after the tactic is built reaches it at the next updt_params
        pipeline pl;
        ENSURE_EQ(pl.flats(params_ref()), "TTT");
        gparams::set("tactic.test_scope.inner.flat", "false");
        ENSURE_EQ(pl.flats(params_ref()), "TFT");
    }
}

static void tst_enabled() {
    gparams_reset _r;
    ENSURE_EQ(runs(params_ref()), "111");
    ENSURE_EQ(runs(mk({{"test_scope.inner.enabled", false}})), "100");
    ENSURE_EQ(runs(mk({{"tactic.test_scope.inner.enabled", false}})), "100");
    ENSURE_EQ(runs(mk({{"test_scope.enabled", false}})), "000");
    ENSURE_EQ(runs(mk({{"test_scope.inner.enabled", true}})), "111");
    // an unscoped "enabled" is not read by scopes
    ENSURE_EQ(runs(mk({{"enabled", false}})), "111");
    {
        pipeline pl;
        // enabled is not passed to the step
        pl.runs(mk({{"test_scope.inner.enabled", true}}));
        ENSURE(!pl.b->m_p->contains("enabled"));
        // a later updt_params enables the step again
        ENSURE_EQ(pl.runs(mk({{"test_scope.inner.enabled", false}})), "100");
        ENSURE_EQ(pl.runs(params_ref()), "111");
    }
    {
        gparams_reset r;
        gparams::set("tactic.test_scope.inner.enabled", "false");
        ENSURE_EQ(runs(params_ref()), "100");
        // local beats global
        ENSURE_EQ(runs(mk({{"test_scope.inner.enabled", true}})), "111");
        // a scope built while the global key is set is disabled before any updt_params
        record_tactic * s = alloc(record_tactic);
        tactic_ref t = scope_tactic("test_scope.inner", s);
        ast_manager m;
        reg_decl_plugins(m);
        goal_ref g = alloc(goal, m);
        goal_ref_buffer result;
        (*t)(g, result);
        ENSURE(s->m_runs == 0 && result.size() == 1);
        // translate keeps the setting: the copy skips fail after the key is reset
        tactic_ref f = scope_tactic("test_scope.inner", mk_fail_tactic());
        ast_manager m2;
        reg_decl_plugins(m2);
        tactic_ref f2 = f->translate(m2);
        gparams::reset();
        goal_ref g2 = alloc(goal, m2);
        result.reset();
        (*f2)(g2, result);
        ENSURE(result.size() == 1);
    }
}

// The keys are validated: globally by their rows in the tactic module, locally by the
// descriptors of the scopes.
static void tst_validation() {
    gparams_reset _r;
    bool thrown = false;
    try {
        gparams::set("tactic.test_scope.inner.flatt", "false");
    }
    catch (z3_exception &) {
        thrown = true;
    }
    ENSURE(thrown);
    gparams::set("tactic.test_scope.inner.flat", "false");
    pipeline pl;
    param_descrs d;
    pl.t->collect_param_descrs(d);
    ENSURE(d.get_kind("test_scope.inner.flat") == CPK_BOOL);
    ENSURE(d.get_kind("test_scope.inner.enabled") == CPK_BOOL);
    ENSURE(d.get_kind("test_scope.flat") == CPK_BOOL);
    params_ref ok = mk({{"test_scope.inner.flat", false}, {"tactic.test_scope.inner.enabled", false}});
    ok.validate(d);
    // an inner scope declares only its own keys
    param_descrs inner;
    tactic_ref t = scope_tactic("test_scope.inner", mk_skip_tactic());
    t->collect_param_descrs(inner);
    ENSURE(inner.get_kind("test_scope.inner.flat") == CPK_BOOL);
    ENSURE(inner.get_kind("test_scope.flat") == CPK_INVALID);
    thrown = false;
    try {
        params_ref typo = mk({{"test_scope.inner.flatt", false}});
        typo.validate(d);
    }
    catch (z3_exception &) {
        thrown = true;
    }
    ENSURE(thrown);
}

// A using_params between two scopes for the same key: its forced value is local for
// the inner scope, though the outer scope took the key from a global setting. The
// display does not mark it "(global)".
static void tst_forced_between_scopes() {
    gparams_reset _r;
    gparams::set("tactic.test_scope.inner.flat", "false");
    record_tactic * rec = alloc(record_tactic);
    params_ref forced;
    forced.set_bool("flat", true);
    tactic_ref t = scope_tactic("test_scope.inner",
                                using_params(scope_tactic("test_scope.inner", rec), forced));
    t->updt_params(params_ref());
    ENSURE(rec->flat());
    std::ostringstream out;
    display_tactic(out, *t, params_ref(), nullptr, true);
    // the step's line: the outer scope's routed value is marked "(global)", the value
    // the step gets is not
    std::string text = out.str(), line;
    std::istringstream lines(text);
    for (std::string l; std::getline(lines, l); )
        if (l.find("active:") != std::string::npos)
            line = l;
    if (line.find(":flat true") == std::string::npos || line.find("(global)") != std::string::npos)
        std::cerr << text;
    ENSURE(line.find("active: :flat true") != std::string::npos);
    ENSURE(line.find("(global)") == std::string::npos);
}

// Both spellings of a local scoped key: <path>.<key> wins, in either order.
static void tst_both_spellings() {
    ENSURE_EQ(flats(mk({{"tactic.test_scope.inner.flat", true}, {"test_scope.inner.flat", false}})), "TFT");
    ENSURE_EQ(flats(mk({{"test_scope.inner.flat", false}, {"tactic.test_scope.inner.flat", true}})), "TFT");
    ENSURE_EQ(runs(mk({{"tactic.test_scope.inner.enabled", true}, {"test_scope.inner.enabled", false}})), "100");
}

// A parameter probe reads its key from updt_params, through cond and fail-if, and a
// translated copy has its own value.
static bool fails(tactic & t) {
    ast_manager m;
    reg_decl_plugins(m);
    goal_ref g = alloc(goal, m);
    goal_ref_buffer result;
    try {
        t(g, result);
    }
    catch (tactic_exception &) {
        return true;
    }
    return false;
}

static void tst_param_probe() {
    params_ref none, low;
    low.set_uint("bound", 1);
    // fails while 5 < bound
    tactic_ref t = when(mk_lt(mk_const_probe(5), mk_param_probe("bound", 10)), mk_fail_tactic());
    tactic_ref f = fail_if(mk_lt(mk_const_probe(5), mk_param_probe("bound", 10)));
    for (tactic * x : { t.get(), f.get() }) {
        ENSURE(fails(*x));
        x->updt_params(low);
        ENSURE(!fails(*x));
        x->updt_params(none);
        ENSURE(fails(*x));
        ast_manager m2;
        reg_decl_plugins(m2);
        tactic_ref x2 = x->translate(m2);
        x2->updt_params(low);
        ENSURE(!fails(*x2));
        ENSURE(fails(*x));
    }
    // display: the value as a constant, the key in the annotation
    std::ostringstream out, ann;
    display_tactic(out, *t, low);
    display_tactic(ann, *t, none, nullptr, true);
    ENSURE(out.str() == "(when (< 5 1) fail)\n");
    ENSURE(ann.str().find("(when (< 5 10) fail) ; probe: bound 10 (default)") != std::string::npos);
    // parseability follows the displayed value: the parser reads 32-bit constants
    params_ref big;
    big.set_uint("bound", 3000000000u);
    std::ostringstream o1, o2;
    display_tactic(o1, *t, big);
    ENSURE(o1.str().find("(< 5 3000000000)) ; not parseable: constant too big") != std::string::npos ||
           o1.str().find("not parseable: constant too big") != std::string::npos);
    t->updt_params(big);
    display_tactic(o2, *t, none);
    ENSURE(o2.str().find("not parseable") == std::string::npos);
    tactic_ref c = when(mk_lt(mk_const_probe(1e12), mk_const_probe(1)), mk_fail_tactic());
    std::ostringstream o3;
    display_tactic(o3, *c, none);
    ENSURE(o3.str().find("not parseable: constant too big") != std::string::npos);
}

static void tst_probe_clone() {
    probe_ref p(mk_memory_probe());
    probe_ref p_copy(p->clone());
    ENSURE(p.get() != p_copy.get());

    probe_ref q(mk_lt(mk_const_probe(1), mk_const_probe(2)));
    probe_ref q_copy(q->clone());
    ENSURE(q.get() != q_copy.get());
}

static void tst_goal_subgoal_policy() {
    ast_manager m, m2;
    goal_ref original = alloc(goal, m);
    original->set_keep_sat_subgoals(true);
    goal_ref copy = alloc(goal, *original);
    goal_ref config = alloc(goal, *original, true);
    goal_ref target = alloc(goal, m);
    target->copy_from(*original);
    ast_translation translator(m, m2, false);
    goal_ref translated = original->translate(translator);
    ENSURE(copy->keep_sat_subgoals());
    ENSURE(config->keep_sat_subgoals());
    ENSURE(target->keep_sat_subgoals());
    ENSURE(translated->keep_sat_subgoals());
    original->set_keep_sat_subgoals(false);
    target->copy_from(*original);
    ENSURE(!target->keep_sat_subgoals());
    ENSURE(copy->keep_sat_subgoals());
}

void tst_tactic_scope() {
    tst_local();
    tst_global();
    tst_enabled();
    tst_validation();
    tst_forced_between_scopes();
    tst_both_spellings();
    tst_param_probe();
    tst_probe_clone();
    tst_goal_subgoal_policy();
}
