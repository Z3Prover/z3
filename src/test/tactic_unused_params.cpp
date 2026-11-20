/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    tactic_unused_params.cpp

Abstract:

    Check that the built-in tactics do not set parameters that no step reads.

    display_tactic marks a parameter set by using_params as unused if no tactic
    of the pipeline declares it in collect_param_descrs (see using_params_tactical).
    The test displays every tactic registered in a cmd_context and fails on a
    flagged parameter that is not in the list below.

    It also checks that the output of display-tactic is valid input: displaying
    the tactic it parses to gives the same text, for every tactic whose output
    has no "not parseable" comment.

--*/
#include <cstring>
#include <iostream>
#include <sstream>
#include "ast/reg_decl_plugins.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/tactic_cmds.h"
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "parsers/smt2/smt2parser.h"
#include "util/debug.h"
#include "util/gparams.h"

// Known flagged parameters, pending a maintainer decision on each.
// Remove an entry when the setter is fixed; the test fails on stale entries.
static char const * const g_known_unused[] = {
    // no step reads these (the reader was removed or never existed):
    "gaussian_max_occs",        // tactic/sls/sls_tactic.cpp
    "skolemize",                // tactic/arith/purify_arith_tactic.cpp
    "array.simplify",           // tactic/smtlogics/qfauflia_tactic.cpp
    "max_power",                // math/subpaving/tactic/subpaving_tactic.cpp
    "use_ls",                   // tactic/smtlogics/qfnra_tactic.cpp
    "ls_time",                  // tactic/smtlogics/qfnra_tactic.cpp
};

static bool is_known(symbol const & k) {
    for (char const * n : g_known_unused)
        if (k == n)
            return true;
    return false;
}

// using_params marks the parameters that nothing reads, and default values.
static void tst_display() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    p.set_bool("som", true);
    p.set_default_bool("flat", false);
    p.set_uint("no_such_parameter", 1);
    tactic_ref t = using_params(mk_simplify_tactic(m), p);
    svector<symbol> unused;
    std::ostringstream out;
    display_tactic(out, *t, params_ref(), &unused, true);
    std::string s = out.str();
    // keys simplify declares are syntax, the others go in the comment
    ENSURE(s.find(":som true :flat false)") != std::string::npos);
    ENSURE(s.find("not parseable: :flat false (default), :no_such_parameter 1 [unused]") != std::string::npos);
    ENSURE(unused.size() == 1);
    // without annotation the default is plain syntax and has no mark
    std::ostringstream plain;
    display_tactic(plain, *t, params_ref());
    s = plain.str();
    ENSURE(s.find(":som true :flat false)") != std::string::npos);
    ENSURE(s.find("(default)") == std::string::npos);
    ENSURE(s.find("not parseable: :no_such_parameter 1 [unused]") != std::string::npos);
}

// A step shows the value in effect for a default: the global value of the key's
// module if the user set one there.
static void tst_display_global() {
    ast_manager m;
    reg_decl_plugins(m);
    params_ref p;
    p.set_default_bool("flat", true);
    p.set_bool("som", true);
    tactic_ref t = using_params(mk_simplify_tactic(m), p);
    auto display = [&]() {
        std::ostringstream out;
        display_tactic(out, *t, params_ref(), nullptr, true);
        return out.str();
    };
    std::string s = display();
    ENSURE(s.find(":flat true (default)") != std::string::npos);
    ENSURE(s.find("(global)") == std::string::npos);
    gparams::set("rewriter.flat", "false");
    gparams::set("rewriter.som", "false");
    s = display();
    gparams::reset();
    // the default yields to the global value, the forced som does not
    ENSURE(s.find(":flat false (global)") != std::string::npos);
    ENSURE(s.find(":som true") != std::string::npos);
    ENSURE(s.find(":som false") == std::string::npos);
}

// Display a tactic with the display-tactic command, the way a user does.
static std::string display_cmd(cmd_context & ctx, std::string const & tactic) {
    std::ostringstream out, err;
    ctx.set_regular_stream(out);
    ctx.set_diagnostic_stream(err);
    std::istringstream in("(display-tactic " + tactic + ")");
    bool ok = parse_smt2_commands(ctx, in);
    ctx.set_regular_stream(std::cout);
    ctx.set_diagnostic_stream(std::cerr);
    if (!ok || !err.str().empty() || out.str().find("(error") != std::string::npos) {
        std::cerr << "display-tactic failed on\n" << tactic << "\n" << out.str() << err.str();
        ENSURE(false);
    }
    return out.str();
}

// Display every registered tactic, with the parameters check-sat-using passes to it.
// - It fails on a flagged parameter that is not in g_known_unused.
// - A tactic registered as a single step displays as its registered name.
// - The output is a tactic: displaying the tactic it parses to gives the same text,
//   unless it says that something is not parseable.
static void tst_tactics() {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context ctx(false, &m);
    params_ref p = ctx.params().merge_default_params(params_ref());
    svector<symbol> all_unused;
    unsigned num_tactics = 0, num_round_trip = 0;
    std::string not_parseable;
    for (tactic_cmd * cmd : ctx.tactics()) {
        std::string name = cmd->get_name().str();
        tactic_ref t = cmd->mk(m);
        svector<symbol> unused;
        std::ostringstream out;
        display_tactic(out, *t, p, &unused);
        std::string s1 = out.str();
        ++num_tactics;
        for (symbol const & k : unused) {
            if (!is_known(k)) {
                std::cerr << "tactic " << name << " sets parameter " << k
                          << " that no step declares\n" << s1;
                ENSURE(false);
            }
            all_unused.push_back(k);
        }
        // psat builds sat unless parallel.enable is set
        if (s1.find('\n') == s1.size() - 1 && s1[0] != '(' && name != "psat") {
            std::string leaf = s1.substr(0, s1.find_first_of(" \n"));
            if (leaf != name) {
                std::cerr << "tactic " << name << " displays as " << leaf << "\n";
                ENSURE(false);
            }
        }
        if (s1.find("not parseable") != std::string::npos) {
            not_parseable += " " + name;
            continue;
        }
        std::string s2 = display_cmd(ctx, s1);
        if (s1 != s2) {
            std::cerr << "tactic " << name << " does not round-trip:\n" << s1 << "--- displays as\n" << s2;
            ENSURE(false);
        }
        ++num_round_trip;
    }
    ENSURE(num_tactics > 100);
    for (char const * n : g_known_unused) {
        if (!all_unused.contains(symbol(n))) {
            std::cerr << "parameter " << n << " is no longer flagged: remove it from the list\n";
            ENSURE(false);
        }
    }
    std::cout << "display-tactic round-trips " << num_round_trip << " of " << num_tactics
              << " tactics; not parseable:" << not_parseable << "\n";
    ENSURE(num_round_trip > 90);
}

void tst_tactic_unused_params() {
    tst_display();
    tst_display_global();
    tst_tactics();
}
