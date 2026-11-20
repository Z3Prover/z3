/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    qfbv_default_params.cpp

Abstract:

    The QF_BV preamble sets its tuned rewriter values as defaults: a value the
    user gives, locally or in the global module of the key, replaces them, also
    when it is given after the tactic is built. The other values stay forced.

--*/
#include <array>
#include <cctype>
#include <iostream>
#include <memory>
#include <sstream>
#include "ast/reg_decl_plugins.h"
#include "ast/bv_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/tactic_cmds.h"
#include "parsers/smt2/smt2parser.h"
#include "tactic/goal.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/qfbv_tactic_params.hpp"
#include "tactic/tactical.h"
#include "solver/solver.h"
#include "util/gparams.h"
#include "util/debug.h"

namespace {

    // Sets a global parameter module.key for the scope of the object. A key that
    // was not set before is unset by resetting all global parameters: setting it
    // back to its default value would leave it set, and a set global value
    // replaces a default.
    struct scoped_gparam {
        std::string m_key, m_saved;
        bool m_was_set;
        scoped_gparam(char const * module, char const * key, char const * v) :
            m_key(std::string(module) + "." + key),
            m_saved(gparams::get_value(m_key.c_str())),
            m_was_set(gparams::get_module(module).contains(key)) {
            gparams::set(m_key.c_str(), v);
        }
        ~scoped_gparam() {
            if (m_was_set)
                gparams::set(m_key.c_str(), m_saved.c_str());
            else
                gparams::reset();
        }
    };

    // The leaves of the display of t with params p, as "name ; comment".
    void leaves(tactic_display_ctx::node const & n, std::vector<std::string> & out) {
        if (n.is_leaf) {
            out.push_back(n.comment.empty() ? n.head : n.head + " ; " + n.comment);
            return;
        }
        for (auto const & c : n.children)
            leaves(c, out);
    }

    std::vector<std::string> display_leaves(tactic & t, params_ref const & p) {
        tactic_display_ctx ctx;
        ctx.annotate = true; // the tests below look at the "(default)" marks
        t.display_pipeline(p, ctx);
        std::vector<std::string> r;
        for (auto const & n : ctx.roots())
            leaves(n, r);
        return r;
    }

    void erase_all(std::string & s, std::string const & w) {
        for (size_t i; (i = s.find(w)) != std::string::npos; )
            s.erase(i, w.size());
    }

    // the lines of display-tactic for the tactic expression e, with the marks of
    // :annotate true unless annotate is false
    std::vector<std::string> display_cmd_leaves(std::string const & e, bool annotate = true) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context ctx(false, &m);
        std::ostringstream out, err;
        ctx.set_regular_stream(out);
        ctx.set_diagnostic_stream(err);
        std::istringstream in("(display-tactic " + e + (annotate ? " :annotate true" : "") + ")");
        bool ok = parse_smt2_commands(ctx, in);
        ctx.set_regular_stream(std::cout);
        ctx.set_diagnostic_stream(std::cerr);
        ENSURE(ok && err.str().empty() && out.str().find("(error") == std::string::npos);
        std::vector<std::string> r;
        std::istringstream lines(out.str());
        for (std::string l; std::getline(lines, l); )
            r.push_back(l);
        return r;
    }

    // the line of the second simplify pass of the preamble: the only one with local_ctx_limit
    std::string simp2(std::vector<std::string> const & ls) {
        std::string r;
        for (auto const & l : ls)
            if (l.find("simplify ;") != std::string::npos && l.find(":local_ctx_limit") != std::string::npos) {
                ENSURE(r.empty());
                r = l;
            }
        ENSURE(!r.empty());
        return r;
    }

    // the first solve-eqs line of the preamble, the one with parameters
    std::string solve_eqs_line(std::vector<std::string> const & ls) {
        for (auto const & l : ls)
            if (l.find("solve-eqs ;") != std::string::npos)
                return l;
        ENSURE(false);
        return "";
    }

    // Apply the preamble to fmls. p is given at construction, then
    // late, if not null, through updt_params as tactic2solver does before a check.
    expr_ref_vector run_preamble(ast_manager & m, expr_ref_vector const & fmls, params_ref const & p,
                                 params_ref const * late = nullptr) {
        tactic_ref t = mk_qfbv_preamble(m, p);
        t->updt_params(p); // as mk_qfbv_tactic does
        if (late)
            t->updt_params(*late);
        goal_ref g = alloc(goal, m);
        for (expr * f : fmls)
            g->assert_expr(f);
        goal_ref_buffer result;
        (*t)(g, result);
        ENSURE(result.size() == 1);
        expr_ref_vector r(m);
        for (unsigned i = 0; i < result[0]->size(); ++i)
            r.push_back(result[0]->form(i));
        return r;
    }

    struct bv_fixture {
        ast_manager m;
        bv_util bv;
        expr_ref x, y, z;
        bv_fixture() : bv(init()), x(m), y(m), z(m) {
            sort_ref s(bv.mk_sort(8), m);
            x = m.mk_const("x", s);
            y = m.mk_const("y", s);
            z = m.mk_const("z", s);
        }
        ast_manager & init() { reg_decl_plugins(m); return m; }
    };
}


// The display-tactic output of e (plain mode), as one string.
static std::string display_cmd_text(std::string const & e) {
    std::string text;
    for (auto const & l : display_cmd_leaves(e, false))
        text += l + "\n";
    return text;
}

// The output of display-tactic parses and displays as itself.
static void ensure_round_trip(std::string const & text) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);
    std::ostringstream out, err;
    ctx.set_regular_stream(out);
    ctx.set_diagnostic_stream(err);
    std::istringstream in("(display-tactic " + text + ")");
    bool ok = parse_smt2_commands(ctx, in);
    ctx.set_regular_stream(std::cout);
    ctx.set_diagnostic_stream(std::cerr);
    ENSURE(ok && err.str().empty());
    if (out.str() != text)
        std::cerr << text << "--- displays as\n" << out.str();
    ENSURE(out.str() == text);
}

// With no user setting, every step gets the same parameters as before the values
// became defaults. The list is the display of qfbv before the change, with
// the "(default)" marks removed.
static void tst_defaults_unchanged() {
    char const * const expected[] = {
        "simplify ; active: :elim_and true :push_ite_bv true :blast_distinct true :flat_and_or false",
        "propagate-values ; active: :elim_and true :push_ite_bv true :blast_distinct true :flat_and_or false",
        "solve-eqs ; active: :solve_eqs.max_occs 2",
        "elim-uncnstr",
        "bv-divrem-bounds",
        "reduce-bv-size",
        "simplify ; active: :elim_and true :push_ite_bv false :blast_distinct true :som true :pull_cheap_ite true :local_ctx true :local_ctx_limit 10000000 :flat true :hoist_mul false :flat_and_or false",
        "simplify ; active: :elim_and true :push_ite_bv true :blast_distinct true :hoist_mul true :som false :flat_and_or false",
        "max-bv-sharing",
        "ackermannize_bv",
        "bv1-blast",
        "smt ; active: :preprocess false",
        "bit-blast",
        "simplify ; active: :elim_and true :push_ite_bv true :blast_distinct true :local_ctx true :flat false :flat_and_or false",
        "solve-eqs",
        "aig",
        "simplify ; active: :elim_and true :push_ite_bv true :blast_distinct true",
        "smt",
        "sat",
        "smt",
    };
    ast_manager m;
    reg_decl_plugins(m);
    tactic_ref t = mk_qfbv_tactic(m, params_ref());
    std::vector<std::string> ls = display_leaves(*t, params_ref());
    bool ok = ls.size() == std::size(expected);
    for (unsigned i = 0; ok && i < ls.size(); ++i) {
        erase_all(ls[i], " (default)");
        // the annotation of a scope around a single step is on its line
        size_t sc = ls[i].find("; scope ");
        if (sc != std::string::npos)
            ls[i].erase(sc > 0 && ls[i][sc - 1] == ' ' ? sc - 1 : sc);
        ok = ls[i] == expected[i];
    }
    if (!ok) {
        std::cerr << "qfbv steps:\n";
        for (auto const & l : ls)
            std::cerr << l << "\n";
    }
    ENSURE(ok);
}

// By default display-tactic shows no marks and its output is a tactic that
// displays as itself; :annotate true adds the marks.
static void tst_display_default_mode() {
    std::vector<std::string> ls = display_cmd_leaves("qfbv", false);
    std::string text;
    for (auto const & l : ls)
        text += l + "\n";
    ENSURE(text.find("(default)") == std::string::npos);
    ENSURE(text.find("(global)") == std::string::npos);
    ENSURE(text.find("not parseable") == std::string::npos);
    // the tactic language has no scopes: they are not shown
    ENSURE(text.find("scope") == std::string::npos);
    ENSURE(text.find("skip") == std::string::npos);
    // round trip: the output parses and displays as itself
    ensure_round_trip(text);
    // the annotated mode has the marks
    std::string a;
    for (auto const & l : display_cmd_leaves("qfbv"))
        a += l + "\n";
    ENSURE(a.find("(default)") != std::string::npos);
    // and names the scopes
    for (char const * sc : { "qfbv", "qfbv.preamble", "qfbv.preamble.solve_eqs", "qfbv.preamble.simp2", "qfbv.preamble.hoist" }) {
        std::string h = std::string("scope ") + sc;
        bool found = false;
        for (size_t i = a.find(h); !found && i != std::string::npos; i = a.find(h, i + 1)) {
            char c = a[i + h.size()];
            found = c != '.' && c != '_' && !isalnum(static_cast<unsigned char>(c));
        }
        ENSURE(found);
    }
    {
        scoped_gparam g("rewriter", "flat", "false");
        text.clear();
        for (auto const & l : display_cmd_leaves("qfbv", false))
            text += l + "\n";
    }
    ENSURE(text.find("(global)") == std::string::npos);
    // the default flat of the second simplify pass is written with the global value
    // that replaces it (the pass is the one with local_ctx_limit)
    ENSURE(text.find(":local_ctx_limit 10000000 :flat false") != std::string::npos);
    ENSURE(text.find(":local_ctx_limit 10000000 :flat true") == std::string::npos);
}

// A user's flat=false reaches the second simplify pass: given locally around
// qfbv, or globally as rewriter.flat=false.
static void tst_display_overrides() {
    std::string l = simp2(display_cmd_leaves("(using-params qfbv :flat false)"));
    ENSURE(l.find(":flat false") != std::string::npos);
    ENSURE(l.find(":flat true") == std::string::npos);
    {
        scoped_gparam g("rewriter", "flat", "false");
        l = simp2(display_cmd_leaves("qfbv"));
    }
    ENSURE(l.find(":flat false (global)") != std::string::npos);
    // forced values do not yield, locally or globally
    l = simp2(display_cmd_leaves("(using-params qfbv :flat_and_or true :pull_cheap_ite false)"));
    ENSURE(l.find(":flat_and_or false") != std::string::npos);
    ENSURE(l.find(":pull_cheap_ite true") != std::string::npos);
    ENSURE(l.find(":flat_and_or true") == std::string::npos);
    ENSURE(l.find(":pull_cheap_ite false") == std::string::npos);
    {
        scoped_gparam g("rewriter", "local_ctx", "false");
        l = simp2(display_cmd_leaves("qfbv"));
    }
    ENSURE(l.find(":local_ctx true") != std::string::npos);
    ENSURE(l.find("(global)") == std::string::npos);
    // solve-eqs shows its default, and the global value that replaces it
    l = solve_eqs_line(display_cmd_leaves("qfbv"));
    ENSURE(l.find(":solve_eqs.max_occs 2 (default)") != std::string::npos);
    {
        scoped_gparam g("tactic", "solve_eqs.max_occs", "5");
        l = solve_eqs_line(display_cmd_leaves("qfbv"));
    }
    ENSURE(l.find(":solve_eqs.max_occs 5 (global)") != std::string::npos);
    ENSURE(l.find(":solve_eqs.max_occs 2") == std::string::npos);
}

// Global settings (module, key, value) for the scope of the object.
struct gsettings {
    std::vector<std::unique_ptr<scoped_gparam>> m_gs;
    gsettings(std::vector<std::array<char const *, 3>> const & kvs) {
        for (auto const & kv : kvs)
            m_gs.push_back(std::make_unique<scoped_gparam>(kv[0], kv[1], kv[2]));
    }
};

// The statistics, without time and memory, and the result goals of the strategy text
// applied to a QF_BV goal on which the scoped keys of tst_scope_replay have an effect.
static std::string run_text(std::string const & text) {
    bv_fixture f;
    auto & bv = f.bv;
    cmd_context ctx(false, &f.m);
    std::istringstream is(text);
    sexpr_ref se = parse_sexpr(ctx, is, params_ref(), "");
    ENSURE(se);
    tactic_ref t = sexpr2tactic(ctx, se.get());
    t->updt_params(params_ref());
    goal_ref g = alloc(goal, f.m, false, true, false);
    g->assert_expr(f.m.mk_eq(f.x, bv.mk_bv_add(f.y, f.z)));
    g->assert_expr(bv.mk_ult(bv.mk_bv_mul(f.x, f.y), f.z));
    g->assert_expr(bv.mk_ult(bv.mk_bv_xor(f.x, bv.mk_bv_xor(f.y, f.z)), bv.mk_bv_add(f.x, f.y)));
    g->assert_expr(bv.mk_ult(bv.mk_bv_mul(bv.mk_bv_add(f.x, f.y), bv.mk_bv_add(f.z, f.y)), bv.mk_bv_xor(f.z, f.x)));
    goal_ref_buffer result;
    (*t)(g, result);
    t->cleanup();
    statistics st;
    t->collect_statistics(st);
    std::ostringstream out;
    for (unsigned i = 0; i < st.size(); ++i) {
        std::string k = st.get_key(i);
        if (k.find("time") != std::string::npos || k.find("memory") != std::string::npos)
            continue;
        out << k << " ";
        if (st.is_uint(i))
            out << st.get_uint_value(i) << "\n";
        else
            out << st.get_double_value(i) << "\n";
    }
    for (goal * r : result)
        r->display(out);
    return out.str();
}

// Replay: the plain display of e under the global settings gs, run as a strategy under
// the global settings rs, gives every step the same effective parameters and does
// the same: same statistics and result on a goal. Returns the display.
static std::string check_replay(std::string const & e, std::vector<std::array<char const *, 3>> const & gs,
                                std::vector<std::array<char const *, 3>> const & rs) {
    std::string text, run;
    std::vector<std::string> original;
    {
        gsettings g(gs);
        text = display_cmd_text(e);
        original = display_cmd_leaves(e, false);
        run = run_text(e);
    }
    gsettings r(rs);
    std::vector<std::string> replay = display_cmd_leaves(text, false);
    if (replay != original) {
        std::cerr << "display of " << e << ":\n" << text << "--- replayed:\n";
        for (auto const & x : replay)
            std::cerr << x << "\n";
    }
    ENSURE(replay == original);
    ensure_round_trip(text);
    std::string rerun = run_text(text);
    if (rerun != run) {
        std::cerr << "run of " << e;
        for (auto const & kv : gs)
            std::cerr << " " << kv[0] << "." << kv[1] << "=" << kv[2];
        std::cerr << ":\n" << run << "--- replayed " << text << ":\n" << rerun;
    }
    ENSURE(rerun == run);
    return text;
}

// Replay with scoped settings: a global scoped key, a local scoped key, and a step
// disabled globally, replayed without them. Also user values that replace author
// defaults outside scopes, locally, and globally (replayed under the same global).
static void tst_scope_replay() {
    std::string const e = "(using-params qfbv :qfbv.preamble.solve_eqs.max_occs 7)";
    std::string text = check_replay(e, { { "tactic", "qfbv.preamble.simp2.flat", "false" },
                                         { "tactic", "qfbv.preamble.hoist.enabled", "false" } }, {});
    // the settings are in it
    std::string l = simp2(display_cmd_leaves(text));
    ENSURE(l.find(":flat false") != std::string::npos);
    ENSURE(text.find(":solve_eqs.max_occs 7") != std::string::npos);
    ENSURE(text.find(":solve_eqs.max_occs 2") == std::string::npos);
    // the hoist pass is skipped: no step has its hoist_mul=true
    for (auto const & x : display_cmd_leaves(text))
        ENSURE(x.find(":hoist_mul true") == std::string::npos);
    ENSURE(text.find("skip") != std::string::npos);
    // no scope syntax
    ENSURE(text.find("scope") == std::string::npos);
    // the settings change what qfbv does on the goal of run_text
    ENSURE(run_text(e) != run_text(text));
    // user values that replace defaults outside scopes
    text = check_replay("(using-params qfbv :flat false)", {}, {});
    ENSURE(text.find(":local_ctx_limit 10000000 :flat false") != std::string::npos);
    text = check_replay("qfbv", { { "rewriter", "flat", "false" } }, { { "rewriter", "flat", "false" } });
    ENSURE(text.find(":local_ctx_limit 10000000 :flat false") != std::string::npos);
}

// After bit-blasting, while the process has allocated fewer than qfbv.aig.max_memory
// megabytes, simplify, solve-eqs and aig run; each has an enabled switch. The goal
// x = y + z, x*y < z with the preamble's solve-eqs disabled, so that solve-eqs-elim-vars
// counts the solve-eqs after bit-blasting. The back ends are skip: the result is the
// goal after the post-blast steps.
struct postblast_run {
    unsigned    elim_vars;
    std::string goal;
    std::string stats;  // the statistics without time and memory
};

static postblast_run run_postblast(params_ref const & p, params_ref const * late = nullptr) {
    bv_fixture f;
    auto & bv = f.bv;
    params_ref q;
    q.copy(p);
    q.set_bool("qfbv.preamble.solve_eqs.enabled", false);
    q.set_bool("qfbv.preamble.simp2.enabled", false); // leave work for the simplify after bit-blasting
    tactic_ref t = mk_qfbv_tactic(f.m, q, mk_skip_tactic(), mk_skip_tactic());
    t->updt_params(q);
    if (late) {
        params_ref r;
        r.copy(*late);
        r.set_bool("qfbv.preamble.solve_eqs.enabled", false);
        r.set_bool("qfbv.preamble.simp2.enabled", false);
        t->updt_params(r);
    }
    goal_ref g = alloc(goal, f.m);
    g->assert_expr(f.m.mk_eq(f.x, bv.mk_bv_add(f.y, f.z)));
    g->assert_expr(bv.mk_ult(bv.mk_bv_mul(f.x, f.y), f.z));
    // (or a (and a b)): simplify with local_ctx reduces it
    expr_ref a(bv.mk_ult(f.y, f.z), f.m), b(bv.mk_ult(f.z, bv.mk_bv_add(f.y, f.y)), f.m);
    g->assert_expr(f.m.mk_or(a, f.m.mk_and(a, b)));
    goal_ref_buffer result;
    (*t)(g, result);
    t->cleanup();
    statistics st;
    t->collect_statistics(st);
    postblast_run r;
    r.elim_vars = 0;
    std::ostringstream ss;
    for (unsigned i = 0; i < st.size(); ++i) {
        if (strcmp(st.get_key(i), "solve-eqs-elim-vars") == 0)
            r.elim_vars += st.get_uint_value(i);
        std::string k = st.get_key(i);
        if (k.find("time") == std::string::npos && k.find("memory") == std::string::npos && st.is_uint(i))
            ss << k << " " << st.get_uint_value(i) << "\n";
    }
    r.stats = ss.str();
    std::ostringstream out;
    for (goal * x : result)
        x->display(out);
    r.goal = out.str();
    return r;
}

// The steps after bit-blasting get a copy of the factory parameters without the scope
// keys; a default (flagged) entry stays a default there, so a later user value replaces
// it.
static void tst_postblast_factory_defaults() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p, late;
    p.set_default_bool("som", true);
    p.set_bool("hoist_mul", true);
    p.set_bool("qfbv.postblast.simp.enabled", false);
    late.set_bool("som", false);
    late.set_bool("hoist_mul", false);
    tactic_ref t = mk_qfbv_tactic(m, p);
    std::string line;
    for (auto const & l : display_leaves(*t, late))
        if (l.find("simplify ;") != std::string::npos && l.find(":local_ctx true :flat false") != std::string::npos)
            line = l;
    if (line.find(":som false") == std::string::npos || line.find(":hoist_mul true") == std::string::npos)
        std::cerr << line << "\n";
    // the default yields to the later value, the user value given at construction stays
    ENSURE(line.find(":som false") != std::string::npos);
    ENSURE(line.find(":hoist_mul true") != std::string::npos);
}

static void tst_postblast() {
    params_ref none, bound0, huge, simp_off, solve_off, aig_off, all_off;
    bound0.set_uint("qfbv.aig.max_memory", 0);
    huge.set_uint("qfbv.aig.max_memory", 1000000);
    simp_off.set_bool("qfbv.postblast.simp.enabled", false);
    solve_off.set_bool("qfbv.postblast.solve_eqs.enabled", false);
    aig_off.set_bool("qfbv.postblast.aig.enabled", false);
    all_off.copy(simp_off);
    all_off.copy(solve_off);
    all_off.copy(aig_off);
    postblast_run d = run_postblast(none);
    ENSURE(d.elim_vars > 0);
    // the bound: below it the steps run, above it they are skipped
    postblast_run r = run_postblast(bound0);
    ENSURE(r.elim_vars == 0 && r.goal != d.goal);
    ENSURE(run_postblast(huge).goal == d.goal);
    // skipping the block is skipping its three steps
    ENSURE(run_postblast(all_off).goal == r.goal);
    // a switch given locally at construction, cleared by a later updt_params: the step
    // runs again
    ENSURE(run_postblast(solve_off, &none).elim_vars == d.elim_vars);
    ENSURE(run_postblast(none, &solve_off).elim_vars == 0);
    // set after construction, either way
    ENSURE(run_postblast(none, &bound0).elim_vars == 0);
    ENSURE(run_postblast(bound0, &none).goal == d.goal);
    // set globally
    {
        scoped_gparam g("tactic", "qfbv.aig.max_memory", "0");
        r = run_postblast(none);
    }
    ENSURE(r.elim_vars == 0);
    // each switch skips its step, the others run
    // solve-eqs and aig normalize the goal: simplify shows with them off
    params_ref solve_aig_off;
    solve_aig_off.copy(solve_off);
    solve_aig_off.copy(aig_off);
    postblast_run sa = run_postblast(solve_aig_off);
    r = run_postblast(all_off);
    ENSURE(r.goal != sa.goal);
    r = run_postblast(simp_off);
    ENSURE(r.elim_vars > 0);
    r = run_postblast(solve_off);
    ENSURE(r.elim_vars == 0 && r.goal != d.goal);
    r = run_postblast(aig_off);
    ENSURE(r.elim_vars > 0 && r.goal != d.goal);
    {
        scoped_gparam g("tactic", "qfbv.postblast.aig.enabled", "false");
        ENSURE(run_postblast(none).goal == r.goal);
    }
    // typos are rejected
    for (char const * k : { "tactic.qfbv.aig.max_memroy", "tactic.qfbv.postblast.aig.enabeld" }) {
        bool thrown = false;
        try {
            gparams::set(k, "0");
        }
        catch (z3_exception &) {
            thrown = true;
        }
        gparams::reset();
        ENSURE(thrown);
    }
    // display: the bound as its value, a disabled step as skip; replay
    std::string text = check_replay("qfbv", { { "tactic", "qfbv.aig.max_memory", "0" } }, {});
    ENSURE(text.find("(< memory 0)") != std::string::npos);
    std::string a;
    {
        scoped_gparam g("tactic", "qfbv.aig.max_memory", "0");
        for (auto const & x : display_cmd_leaves("qfbv"))
            a += x + "\n";
    }
    ENSURE(a.find("probe: aig.max_memory 0 (global)") != std::string::npos);
    a.clear();
    for (auto const & x : display_cmd_leaves("qfbv"))
        a += x + "\n";
    ENSURE(a.find("probe: aig.max_memory 300 (default)") != std::string::npos);
    text = check_replay("(using-params qfbv :qfbv.aig.max_memory 5)", {}, {});
    ENSURE(text.find("(< memory 5)") != std::string::npos);
    // simplify is the only step after bit-blasting that declares the keys of their
    // using-params: disabled, it is displayed as (when 0 simplify), so that solve-eqs
    // still receives them
    for (char const * k : { "qfbv.postblast.solve_eqs.enabled", "qfbv.postblast.aig.enabled", "qfbv.postblast.simp.enabled" }) {
        text = check_replay("qfbv", { { "tactic", k, "false" } }, {});
        ENSURE(text.find(strcmp(k, "qfbv.postblast.simp.enabled") == 0 ? "(when 0 simplify)" : "skip") != std::string::npos);
    }
}

// A key of a using-params that only a disabled step declares: the step is displayed as
// (when 0 t), so that the key can still be written, and the output parses and
// round-trips. Leaving the key out could change what the other steps receive.
static void tst_skipped_key() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    p.set_uint("solve_eqs.max_occs", 5);
    tactic_ref t = using_params(and_then(scope_tactic("qfbv.preamble.solve_eqs", mk_solve_eqs_tactic(m)),
                                         mk_simplify_tactic(m)), p);
    std::string text, a;
    {
        scoped_gparam g("tactic", "qfbv.preamble.solve_eqs.enabled", "false");
        std::ostringstream out, ann;
        display_tactic(out, *t, params_ref());
        display_tactic(ann, *t, params_ref(), nullptr, true);
        text = out.str();
        a = ann.str();
    }
    std::string const expected =
        "(using-params\n"
        "  (then\n"
        "    (when 0 solve-eqs) ; active: :solve_eqs.max_occs 5\n"
        "    simplify)\n"
        "  :solve_eqs.max_occs 5)\n";
    if (text != expected)
        std::cerr << text << a;
    ENSURE(text == expected);
    ensure_round_trip(text);
    ENSURE(a.find("scope qfbv.preamble.solve_eqs disabled (global)") != std::string::npos);
    // a disabled step whose keys no using-params needs is skip
    tactic_ref u = and_then(scope_tactic("qfbv.preamble.solve_eqs", mk_solve_eqs_tactic(m)), mk_simplify_tactic(m));
    {
        scoped_gparam g("tactic", "qfbv.preamble.solve_eqs.enabled", "false");
        std::ostringstream out;
        display_tactic(out, *u, params_ref());
        text = out.str();
    }
    ENSURE(text == "(then skip simplify)\n");
    // enabled, the key is written
    std::ostringstream out;
    display_tactic(out, *t, params_ref());
    ENSURE(out.str().find(":solve_eqs.max_occs 5") != std::string::npos);
    ensure_round_trip(out.str());
}

// A scoped key reaches only the steps of its scope, locally and globally, and the
// display shows a disabled step; the output still round-trips.
static void tst_scope_display() {
    // local: the second simplify pass gets flat=false, the hoist pass keeps its values
    auto ls = display_cmd_leaves("(using-params qfbv :qfbv.preamble.simp2.flat false)");
    std::string l = simp2(ls);
    ENSURE(l.find(":flat false") != std::string::npos);
    for (auto const & x : ls)
        if (x.find(":hoist_mul true") != std::string::npos)
            ENSURE(x.find(":flat ") == std::string::npos);
    // the module prefix is optional locally
    l = simp2(display_cmd_leaves("(using-params qfbv :tactic.qfbv.preamble.simp2.flat false)"));
    ENSURE(l.find(":flat false") != std::string::npos);
    {
        scoped_gparam g("tactic", "qfbv.preamble.simp2.flat", "false");
        l = simp2(display_cmd_leaves("qfbv"));
    }
    ENSURE(l.find(":flat false (global)") != std::string::npos);
    // global scoped beats global unscoped
    {
        scoped_gparam g1("rewriter", "som", "false");
        scoped_gparam g2("tactic", "qfbv.preamble.simp2.som", "true");
        l = simp2(display_cmd_leaves("qfbv"));
    }
    ENSURE(l.find(":som true (global)") != std::string::npos);
    // local unscoped beats global scoped
    {
        scoped_gparam g("tactic", "qfbv.preamble.simp2.flat", "false");
        l = simp2(display_cmd_leaves("(using-params qfbv :flat true)"));
    }
    ENSURE(l.find(":flat true") != std::string::npos);
    ENSURE(l.find(":flat false") == std::string::npos);
    // max_occs of solve-eqs in the preamble
    l = solve_eqs_line(display_cmd_leaves("(using-params qfbv :qfbv.preamble.solve_eqs.max_occs 7)"));
    ENSURE(l.find(":solve_eqs.max_occs 7") != std::string::npos);
    // a disabled step, set locally or globally, is displayed as skip; the scoped key
    // is not written (the tactic it parses to has no scope to read it)
    std::string text = display_cmd_text("(using-params qfbv :qfbv.preamble.solve_eqs.enabled false)");
    ENSURE(text.find("qfbv.preamble") == std::string::npos);
    ENSURE(text.find("skip") != std::string::npos);
    ENSURE(text.find("solve_eqs.max_occs") == std::string::npos);
    ENSURE(text.find("solve-eqs") != std::string::npos); // after bit-blasting
    ensure_round_trip(text);
    std::string a;
    for (auto const & x : display_cmd_leaves("(using-params qfbv :qfbv.preamble.solve_eqs.enabled false)"))
        a += x + "\n";
    ENSURE(a.find("skip ; scope qfbv.preamble.solve_eqs disabled") != std::string::npos);
    ENSURE(a.find("scoped: :qfbv.preamble.solve_eqs.enabled false") != std::string::npos);
    {
        scoped_gparam g("tactic", "qfbv.preamble.solve_eqs.enabled", "false");
        std::string t2 = display_cmd_text("qfbv");
        ENSURE(t2 == text);
        ensure_round_trip(t2);
        a.clear();
        for (auto const & x : display_cmd_leaves("qfbv"))
            a += x + "\n";
        ENSURE(a.find("skip ; scope qfbv.preamble.solve_eqs disabled (global)") != std::string::npos);
    }
    // a scoped value is written on its step
    text = display_cmd_text("(using-params qfbv :qfbv.preamble.simp2.flat false)");
    ENSURE(text.find("qfbv.preamble") == std::string::npos);
    ensure_round_trip(text);
}

// Forced values of the author still win over scoped keys. The key is not declared,
// so only C++ callers, which are not validated, can pass it.
static void tst_scope_forced() {
    ast_manager m;
    reg_decl_plugins(m);
    tactic_ref t = mk_qfbv_tactic(m, params_ref());
    params_ref p;
    p.set_bool("qfbv.preamble.simp2.pull_cheap_ite", false);
    p.set_bool("qfbv.preamble.simp2.flat_and_or", true);
    std::string l = simp2(display_leaves(*t, p));
    ENSURE(l.find(":pull_cheap_ite true") != std::string::npos);
    ENSURE(l.find(":flat_and_or false") != std::string::npos);
    ENSURE(l.find(":pull_cheap_ite false") == std::string::npos);
    ENSURE(l.find(":flat_and_or true") == std::string::npos);
}

// The line of the step a row of qfbv_tactic_params routes to, and the key of the
// step it sets.
static std::string row_step_line(std::vector<std::string> const & ls, std::string const & row, std::string & key) {
    auto starts = [&](char const * pre) {
        if (row.compare(0, strlen(pre), pre) != 0)
            return false;
        key = row.substr(strlen(pre));
        return true;
    };
    if (starts("qfbv.preamble.simp2."))
        return simp2(ls);
    if (starts("qfbv.preamble.hoist.")) {
        // the step after the second simplify pass
        std::string s2 = simp2(ls);
        for (unsigned i = 0; i + 1 < ls.size(); ++i)
            if (ls[i] == s2)
                return ls[i + 1];
    }
    if (starts("qfbv.preamble.solve_eqs.")) {
        key = "solve_eqs." + key;
        return solve_eqs_line(ls);
    }
    ENSURE(false);
    return "";
}

// the leaves of qfbv, annotated
static std::vector<std::string> qfbv_leaves() {
    ast_manager m;
    reg_decl_plugins(m);
    tactic_ref t = mk_qfbv_tactic(m, params_ref());
    return display_leaves(*t, params_ref());
}

// Each row of qfbv_tactic_params is live: set globally to another value than its
// default, it changes the step it names. Its default is the value of the factory.
static void tst_rows_live() {
    std::vector<std::string> base = qfbv_leaves();
    param_descrs d;
    qfbv_tactic_params::collect_param_descrs(d);
    ENSURE(d.size() > 0);
    for (unsigned i = 0; i < d.size(); ++i) {
        symbol k = d.get_param_name(i);
        std::string row = k.str(), def = d.get_default(k), v;
        if (d.get_kind(k) == CPK_BOOL)
            v = def == "true" ? "false" : "true";
        else {
            ENSURE(d.get_kind(k) == CPK_UINT);
            v = std::to_string(std::stoul(def) + 1);
        }
        if (row.size() > 8 && row.compare(row.size() - 8, 8, ".enabled") == 0) {
            ENSURE(def == "true");
            std::string path = row.substr(0, row.size() - 8), text;
            {
                scoped_gparam g("tactic", row.c_str(), v.c_str());
                for (auto const & x : display_cmd_leaves("qfbv"))
                    text += x + "\n";
            }
            // the line of the step is skip (followed by closing parentheses), or
            // (when 0 if an enclosing using-params needs the keys the step declares
            size_t at = text.find("; scope " + path + " disabled");
            bool ok = at != std::string::npos;
            if (ok) {
                size_t bol = text.rfind('\n', at) + 1;
                std::string line = text.substr(bol, at - bol);
                ok = line.find("skip") != std::string::npos || line.find("(when 0") != std::string::npos;
            }
            if (!ok)
                std::cerr << "row has no effect: " << row << "\n" << text;
            ENSURE(ok);
            continue;
        }
        if (row == "qfbv.aig.max_memory") {
            // the bound of the memory probe, displayed as its value
            std::string text = display_cmd_text("qfbv");
            ENSURE(text.find("(< memory " + def + ")") != std::string::npos);
            {
                scoped_gparam g("tactic", row.c_str(), v.c_str());
                text = display_cmd_text("qfbv");
            }
            if (text.find("(< memory " + v + ")") == std::string::npos)
                std::cerr << "row has no effect: " << row << "\n" << text;
            ENSURE(text.find("(< memory " + v + ")") != std::string::npos);
            continue;
        }
        std::string key;
        std::string l = row_step_line(base, row, key);
        if (l.find(":" + key + " " + def) == std::string::npos)
            std::cerr << "default of " << row << " is not the value of the step: " << l << "\n";
        ENSURE(l.find(":" + key + " " + def) != std::string::npos);
        {
            scoped_gparam g("tactic", row.c_str(), v.c_str());
            l = row_step_line(qfbv_leaves(), row, key);
        }
        if (l.find(":" + key + " " + v) == std::string::npos)
            std::cerr << "row has no effect: " << row << " " << v << ": " << l << "\n";
        ENSURE(l.find(":" + key + " " + v) != std::string::npos);
    }
}

// A typo in a scoped key is rejected: globally by the tactic module, locally by the
// descriptors of qfbv.
static void tst_scope_typo() {
    bool thrown = false;
    try {
        gparams::set("tactic.qfbv.preamble.solve_eqs.enabeld", "false");
    }
    catch (z3_exception &) {
        thrown = true;
    }
    gparams::reset();
    ENSURE(thrown);
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);
    std::ostringstream out, err;
    ctx.set_regular_stream(out);
    ctx.set_diagnostic_stream(err);
    std::istringstream in("(display-tactic (using-params qfbv :qfbv.preamble.solve_eqs.enabeld false))");
    parse_smt2_commands(ctx, in);
    ctx.set_regular_stream(std::cout);
    ctx.set_diagnostic_stream(std::cerr);
    ENSURE((out.str() + err.str()).find("unknown parameter") != std::string::npos);
}

// The second simplify pass flattens bvxor under flat=true, and max-bv-sharing
// then splits both ternary bvxor the same way: two distinct bvxor terms remain.
// Without flattening there are four. The hoist pass does not set flat, so the
// count shows the flat of the second pass.
static unsigned num_xor(params_ref const & p, params_ref const * late = nullptr) {
    bv_fixture f;
    auto & bv = f.bv;
    expr_ref_vector fmls(f.m);
    fmls.push_back(bv.mk_ult(bv.mk_bv_xor(f.x, bv.mk_bv_xor(f.y, f.z)), bv.mk_bv_add(f.x, f.y)));
    fmls.push_back(bv.mk_ult(bv.mk_bv_xor(f.z, bv.mk_bv_xor(f.x, f.y)), bv.mk_bv_mul(f.x, f.z)));
    expr_ref_vector r = run_preamble(f.m, fmls, p, late);
    unsigned n = 0;
    for (expr * e : subterms::all(r))
        n += bv.is_bv_xor(e);
    return n;
}

static void tst_flat() {
    params_ref none, flat_false, flat_true;
    flat_false.set_bool("flat", false);
    flat_true.set_bool("flat", true);
    // by default the second pass flattens
    ENSURE(num_xor(none) == 2);
    // flat=false given at construction (using-params, check-sat-using)
    ENSURE(num_xor(flat_false) == 4);
    // flat=false given after construction (solver.set, then check-sat)
    ENSURE(num_xor(none, &flat_false) == 4);
    // a later user value replaces an earlier one
    ENSURE(num_xor(flat_false, &flat_true) == 2);
    // flat=false in the global rewriter module
    unsigned n;
    {
        scoped_gparam g("rewriter", "flat", "false");
        n = num_xor(none);
    }
    ENSURE(n == 4);
}

// som requires flat: with flat=false from the user, the second pass does not
// put polynomials in sum-of-monomials form, even if the user sets som=true
// (the rewriter turns som off without flat). Without som, the product of sums
// (x+1)*(y+1) stays; with it, it is expanded (and partly hoisted again by the
// hoist pass, which does not rebuild a product of two sums).
static bool has_product_of_sums(params_ref const & p, params_ref const * late = nullptr) {
    bv_fixture f;
    auto & bv = f.bv;
    expr_ref one(bv.mk_numeral(1, 8), f.m);
    expr_ref_vector fmls(f.m);
    fmls.push_back(bv.mk_ult(bv.mk_bv_mul(bv.mk_bv_add(f.x, one), bv.mk_bv_add(f.y, one)), bv.mk_bv_mul(f.x, f.y)));
    fmls.push_back(bv.mk_ult(f.x, f.y));
    expr_ref_vector r = run_preamble(f.m, fmls, p, late);
    for (expr * e : subterms::all(r))
        if (bv.is_bv_mul(e) && to_app(e)->get_num_args() == 2 &&
            bv.is_bv_add(to_app(e)->get_arg(0)) && bv.is_bv_add(to_app(e)->get_arg(1)))
            return true;
    return false;
}

static void tst_som_follows_flat() {
    params_ref none, flat_false, flat_false_som_true;
    flat_false.set_bool("flat", false);
    flat_false_som_true.set_bool("flat", false);
    flat_false_som_true.set_bool("som", true);
    ENSURE(!has_product_of_sums(none));
    ENSURE(has_product_of_sums(flat_false));
    ENSURE(has_product_of_sums(none, &flat_false));
    ENSURE(has_product_of_sums(flat_false_som_true));
    bool b;
    {
        scoped_gparam g("rewriter", "flat", "false");
        b = has_product_of_sums(none);
    }
    ENSURE(b);
}

// solve-eqs in the preamble eliminates a variable with at most 2 occurrences,
// unless the user sets solve_eqs_max_occs, or tactic.solve_eqs.max_occs locally or
// globally.
static bool eliminates_x(params_ref const & p) {
    bv_fixture f;
    auto & bv = f.bv;
    expr_ref_vector fmls(f.m);
    fmls.push_back(f.m.mk_eq(f.x, bv.mk_bv_add(f.y, f.z)));
    fmls.push_back(bv.mk_ult(f.x, f.y));
    fmls.push_back(bv.mk_ult(f.x, f.z));
    fmls.push_back(bv.mk_ult(bv.mk_bv_mul(f.x, f.y), f.z));
    expr_ref_vector r = run_preamble(f.m, fmls, p);
    for (expr * e : subterms::all(r))
        if (e == f.x)
            return false;
    return true;
}

static void tst_solve_eqs_max_occs() {
    params_ref none, local_alias, local_key;
    local_alias.set_uint("solve_eqs_max_occs", 100);
    local_key.set_uint("solve_eqs.max_occs", 100);
    ENSURE(!eliminates_x(none));
    ENSURE(eliminates_x(local_alias));
    ENSURE(eliminates_x(local_key));
    bool b;
    {
        scoped_gparam g("tactic", "solve_eqs.max_occs", "100");
        b = eliminates_x(none);
    }
    ENSURE(b);
}

// solve-eqs in the preamble eliminates x (2 occurrences) by default. With
// qfbv.preamble.solve_eqs.enabled=false it does not, and the solve-eqs after
// bit-blasting still runs. smt.solve_eqs=false disables both, and a scoped
// enabled=true does not enable the preamble step again.
struct solve_eqs_run {
    bool     preamble_keeps_x;  // x is in the result of the preamble
    unsigned elim_vars;         // solve-eqs-elim-vars of qfbv without the sat/smt back ends
};

static solve_eqs_run run_solve_eqs(params_ref const & p, params_ref const * late = nullptr) {
    bv_fixture f;
    auto & bv = f.bv;
    expr_ref_vector fmls(f.m);
    fmls.push_back(f.m.mk_eq(f.x, bv.mk_bv_add(f.y, f.z)));
    fmls.push_back(bv.mk_ult(bv.mk_bv_mul(f.x, f.y), f.z));
    solve_eqs_run r;
    r.preamble_keeps_x = false;
    for (expr * e : subterms::all(run_preamble(f.m, fmls, p, late)))
        r.preamble_keeps_x |= e == f.x;
    tactic_ref t = mk_qfbv_tactic(f.m, p, mk_skip_tactic(), mk_skip_tactic());
    t->updt_params(p);
    if (late)
        t->updt_params(*late);
    goal_ref g = alloc(goal, f.m);
    for (expr * e : fmls)
        g->assert_expr(e);
    goal_ref_buffer result;
    (*t)(g, result);
    t->cleanup();
    statistics st;
    t->collect_statistics(st);
    r.elim_vars = 0;
    for (unsigned i = 0; i < st.size(); ++i)
        if (strcmp(st.get_key(i), "solve-eqs-elim-vars") == 0)
            r.elim_vars += st.get_uint_value(i);
    return r;
}

static void tst_solve_eqs_enabled() {
    params_ref none, off, on;
    off.set_bool("qfbv.preamble.solve_eqs.enabled", false);
    on.set_bool("qfbv.preamble.solve_eqs.enabled", true);
    solve_eqs_run d = run_solve_eqs(none);
    ENSURE(!d.preamble_keeps_x);
    ENSURE(d.elim_vars > 0);
    // local, at construction or later
    solve_eqs_run r = run_solve_eqs(off);
    ENSURE(r.preamble_keeps_x);
    // the solve-eqs after bit-blasting eliminates bits of x
    ENSURE(r.elim_vars > 0);
    r = run_solve_eqs(none, &off);
    ENSURE(r.preamble_keeps_x && r.elim_vars > 0);
    r = run_solve_eqs(off, &on);
    ENSURE(!r.preamble_keeps_x);
    {
        scoped_gparam g("tactic", "qfbv.preamble.solve_eqs.enabled", "false");
        r = run_solve_eqs(none);
    }
    ENSURE(r.preamble_keeps_x && r.elim_vars > 0);
    // smt.solve_eqs=false still disables every solve-eqs step
    {
        scoped_gparam g("smt", "solve_eqs", "false");
        r = run_solve_eqs(on);
    }
    ENSURE(r.preamble_keeps_x && r.elim_vars == 0);
}

// The default solver builds the QF_BV tactic lazily; it still declares the keys,
// so a local setting (solver.set) of a scoped key is validated and accepted.
static void tst_default_solver_declares() {
    ast_manager m;
    reg_decl_plugins(m);
    scoped_ptr<solver_factory> f = mk_smt_strategic_solver_factory();
    ref<solver> s = (*f)(m, params_ref(), false, true, false, symbol::null);
    param_descrs d;
    s->collect_param_descrs(d);
    ENSURE(d.get_kind("qfbv.preamble.solve_eqs.enabled") == CPK_BOOL);
    params_ref p;
    p.set_bool("qfbv.preamble.solve_eqs.enabled", false);
    p.validate(d);
    params_ref typo;
    typo.set_bool("qfbv.preamble.solve_eqs.enabeld", false);
    bool thrown = false;
    try {
        typo.validate(d);
    }
    catch (z3_exception &) {
        thrown = true;
    }
    ENSURE(thrown);
}

void tst_qfbv_default_params() {
    tst_defaults_unchanged();
    tst_display_default_mode();
    tst_display_overrides();
    tst_flat();
    tst_som_follows_flat();
    tst_solve_eqs_max_occs();
    tst_scope_display();
    tst_scope_forced();
    tst_rows_live();
    tst_scope_typo();
    tst_solve_eqs_enabled();
    tst_default_solver_declares();
    tst_scope_replay();
    tst_skipped_key();
    tst_postblast();
    tst_postblast_factory_defaults();
}
