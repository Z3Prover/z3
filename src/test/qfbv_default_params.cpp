/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    qfbv_default_params.cpp

Abstract:

    The QF_BV preamble sets its tuned rewriter values as defaults: a value the
    user gives, locally or in the global module of the key, replaces them, also
    when it is given after the tactic is built. The other values stay forced.

--*/
#include <iostream>
#include <sstream>
#include "ast/reg_decl_plugins.h"
#include "ast/bv_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "tactic/goal.h"
#include "tactic/smtlogics/qfbv_tactic.h"
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
    // round trip: the output parses and displays as itself
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
    // the annotated mode has the marks
    std::string a;
    for (auto const & l : display_cmd_leaves("qfbv"))
        a += l + "\n";
    ENSURE(a.find("(default)") != std::string::npos);
    {
        scoped_gparam g("rewriter", "flat", "false");
        text.clear();
        for (auto const & l : display_cmd_leaves("qfbv", false))
            text += l + "\n";
    }
    ENSURE(text.find("(global)") == std::string::npos);
    ENSURE(text.find(":flat false") != std::string::npos);
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

void tst_qfbv_default_params() {
    tst_defaults_unchanged();
    tst_display_default_mode();
    tst_display_overrides();
    tst_flat();
    tst_som_follows_flat();
    tst_solve_eqs_max_occs();
}
