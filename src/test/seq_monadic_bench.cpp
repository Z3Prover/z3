/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic_bench.cpp

Abstract:

    Opt-in benchmark harness for seq_monadic. Reads every *.smt2 under
    Z3_SEQ_BENCH_DIR, extracts regex memberships, and reports CSV timing.
    Z3_SEQ_MONADIC_MODE selects "brz" or "light-ant" (default).

--*/

#define _CRT_SECURE_NO_WARNINGS

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/seq_monadic.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <regex>
#include <sstream>
#include <string>
#include <vector>

namespace {

char const* verdict_str(lbool l) {
    return l == l_true ? "sat" : l == l_false ? "unsat" : "undef";
}

char const* mode_str(seq_monadic::transition_mode mode) {
    switch (mode) {
    case seq_monadic::transition_mode::brzozowski: return "brz";
    case seq_monadic::transition_mode::light_antimirov: return "light-ant";
    }
    UNREACHABLE();
    return "";
}

seq_monadic::transition_mode get_mode() {
    char const* mode = getenv("Z3_SEQ_MONADIC_MODE");
    if (mode && std::string(mode) == "brz")
        return seq_monadic::transition_mode::brzozowski;
    return seq_monadic::transition_mode::light_antimirov;
}

bool is_seq_var(expr* t) {
    return is_app(t) && to_app(t)->get_num_args() == 0 &&
           to_app(t)->get_family_id() == null_family_id;
}

std::string read_status(std::string const& path) {
    std::ifstream in(path);
    std::stringstream ss;
    ss << in.rdbuf();
    std::smatch match;
    std::regex status_re("set-info\\s*:status\\s+(sat|unsat|unknown)");
    std::string text = ss.str();
    return std::regex_search(text, match, status_re) ? match[1].str() : "?";
}

lbool run_file(
    std::string const& path,
    seq_monadic::transition_mode mode,
    double& solve_ms,
    bool& parsed,
    bool& complete) {
    solve_ms = 0;
    parsed = false;
    complete = false;
    cmd_context ctx(false);
    ctx.set_ignore_check(true);
    {
        std::ifstream is(path);
        if (!is.good() || !parse_smt2_commands(ctx, is))
            return l_undef;
    }
    parsed = true;
    ast_manager& m = ctx.m();
    seq_util u(m);
    seq_rewriter rw(m);
    seq_monadic mon(rw, mode);

    obj_map<expr, expr*> var_re;
    obj_map<expr, expr*> term_re;
    ptr_vector<expr> terms;
    expr_ref_vector pin(m);

    std::function<bool(expr*)> collect = [&](expr* a) {
        expr* s = nullptr, * r = nullptr;
        if (m.is_and(a)) {
            for (expr* arg : *to_app(a))
                if (!collect(arg))
                    return false;
            return true;
        }
        if (!u.str.is_in_re(a, s, r))
            return false;
        bool is_var = is_seq_var(s);
        if (!is_var && !u.str.is_concat(s))
            return false;
        obj_map<expr, expr*>& map = is_var ? var_re : term_re;
        expr* previous = nullptr;
        if (map.find(s, previous)) {
            expr_ref intersection = rw.mk_regex_inter_normalize(previous, r);
            pin.push_back(intersection);
            map.insert(s, intersection);
        }
        else {
            map.insert(s, r);
            if (!is_var)
                terms.push_back(s);
        }
        return true;
    };
    complete = true;
    for (expr* assertion : ctx.assertions())
        complete = collect(assertion) && complete;

    vector<std::pair<expr*, expr*>> memberships;
    for (expr* term : terms) {
        expr* r = nullptr;
        term_re.find(term, r);
        memberships.push_back(std::make_pair(term, r));
    }
    for (auto const& entry : var_re)
        memberships.push_back(std::make_pair(entry.m_key, entry.m_value));

    obj_map<expr, expr*> no_extra;
    auto start = std::chrono::high_resolution_clock::now();
    lbool verdict = memberships.empty()
        ? l_undef
        : mon.solve_and(memberships, no_extra, nullptr);
    solve_ms = std::chrono::duration<double, std::milli>(
        std::chrono::high_resolution_clock::now() - start).count();
    return verdict;
}

void display_row(
    std::string const& file,
    std::string const& tier,
    std::string const& status,
    bool complete,
    seq_monadic::transition_mode mode,
    lbool verdict,
    double solve_ms) {
    std::cout << file << "," << tier << "," << status << ","
              << (complete ? "yes" : "no") << "," << mode_str(mode)
              << "," << verdict_str(verdict) << "," << solve_ms
              << "\n";
}

}

void tst_seq_monadic_bench() {
    namespace fs = std::filesystem;
    std::error_code ec;
    seq_monadic::transition_mode mode = get_mode();

    if (char const* file = getenv("Z3_SEQ_BENCH_FILE")) {
        double ms = 0;
        bool parsed = false, complete = false;
        lbool verdict = run_file(file, mode, ms, parsed, complete);
        display_row(file, "", read_status(file), complete, mode, verdict, ms);
        return;
    }

    char const* dir = getenv("Z3_SEQ_BENCH_DIR");
    if (!dir) {
        std::cout << "seq_monadic_bench: set Z3_SEQ_BENCH_DIR; "
                     "optionally set Z3_SEQ_MONADIC_MODE=brz|light-ant\n";
        return;
    }
    if (!fs::exists(dir, ec)) {
        std::cout << "seq_monadic_bench: dir not found: " << dir << "\n";
        return;
    }

    std::vector<std::string> files;
    for (auto& entry : fs::recursive_directory_iterator(dir, ec))
        if (entry.is_regular_file() && entry.path().extension() == ".smt2")
            files.push_back(entry.path().string());
    std::sort(files.begin(), files.end());

    std::cout << "file,tier,status,complete,mode,verdict,solve_ms\n";
    unsigned agree = 0, mismatch = 0, undef = 0, unparsed = 0, incomplete = 0;
    double total_ms = 0;
    for (unsigned i = 0; i < files.size(); ++i) {
        std::string const& file = files[i];
        std::string status = read_status(file);
        std::string relative = fs::relative(file, dir, ec).generic_string();
        std::string tier = relative.substr(0, relative.find('/'));
        std::cerr << "[" << (i + 1) << "/" << files.size() << "] "
                  << relative << std::endl;
        double ms = 0;
        bool parsed = false, complete = false;
        lbool verdict = run_file(file, mode, ms, parsed, complete);
        display_row(relative, tier, status, complete, mode, verdict, ms);
        total_ms += ms;
        if (!parsed) ++unparsed;
        if (!complete) ++incomplete;
        if (verdict == l_undef) ++undef;
        else if (complete && (status == "sat" || status == "unsat")) {
            if (status == verdict_str(verdict)) ++agree;
            else ++mismatch;
        }
    }
    std::cout << "# SUMMARY mode=" << mode_str(mode)
              << " files=" << files.size()
              << " agree=" << agree
              << " mismatch=" << mismatch
              << " undef=" << undef
              << " unparsed=" << unparsed
              << " incomplete=" << incomplete
              << " total_solve_ms=" << total_ms << "\n";
}
