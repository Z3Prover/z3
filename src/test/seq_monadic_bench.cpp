/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic_bench.cpp

Abstract:

    Opt-in benchmark harness for seq_monadic. Reads every *.smt2 under
    Z3_SEQ_BENCH_DIR, extracts regex memberships and length bounds, and reports
    CSV timing.  Z3_SEQ_MONADIC_MODE selects "brz" or "light-ant" (default).

    Assertions the harness cannot hand to seq_monadic are DROPPED.  The CSV
    reports how many were dropped ("dropped") and whether the benchmark was
    modelled in full ("complete").  On an incomplete benchmark only an `unsat`
    verdict carries over to the original problem: dropping conjuncts weakens it,
    so `sat` there says nothing about the benchmark's real status.

--*/

#define _CRT_SECURE_NO_WARNINGS

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
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
    bool& complete,
    unsigned& dropped) {
    solve_ms = 0;
    parsed = false;
    complete = false;
    dropped = 0;
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
    arith_util a(m);
    seq_rewriter rw(m);
    th_rewriter trw(m);
    trail_stack undo_trail;
    seq_monadic mon(rw, undo_trail, mode);

    obj_map<expr, expr*> var_re;
    obj_map<expr, expr*> term_re;
    ptr_vector<expr> terms;
    expr_ref_vector pin(m);

    // Length bounds accumulated per term; lo/hi are the tightest bounds seen.
    struct len_bounds { unsigned lo = 0; unsigned hi = UINT_MAX; };
    obj_map<expr, len_bounds> bounds;
    ptr_vector<expr> bounded;

    // seq_monadic models |t| <= hi as a bounded loop, so a huge hi is not usable.
    const int64_t MAX_LEN_BOUND = 1 << 16;
    const int64_t NO_UPPER = INT64_MAX;

    auto tighten = [&](expr* t, int64_t lo, int64_t hi) {
        if (!is_seq_var(t) && !u.str.is_concat(t))
            return false;
        if (lo > MAX_LEN_BOUND)
            return false;                         // cannot build Sigma^lo
        if (hi != NO_UPPER && hi > MAX_LEN_BOUND)
            return false;                         // dropping it would be unsound
        len_bounds b;
        if (!bounds.find(t, b))
            bounded.push_back(t);
        if (lo > 0)
            b.lo = std::max(b.lo, static_cast<unsigned>(lo));
        if (hi < 0)                               // |t| < 0: record a contradiction
            b.lo = std::max(b.lo, 1u), b.hi = 0;
        else if (hi != NO_UPPER)
            b.hi = std::min(b.hi, static_cast<unsigned>(hi));
        bounds.insert(t, b);
        return true;
    };

    // Recognize a linear length constraint  (str.len t)  <op>  k  (either argument
    // order, optionally negated) and record it as a bound on t.
    std::function<bool(expr*, bool)> collect_len = [&](expr* e, bool sign) {
        expr* arg = nullptr;
        if (m.is_not(e, arg))
            return collect_len(arg, !sign);
        // normalize to  lhs <op> rhs  with op in {<=, <, =}
        expr* lhs = nullptr, * rhs = nullptr;
        bool le = false, lt = false, eq = false;
        if (a.is_le(e, lhs, rhs))      le = true;
        else if (a.is_lt(e, lhs, rhs)) lt = true;
        else if (a.is_ge(e, rhs, lhs)) le = true;      // k >= |t|  ==  |t| <= k
        else if (a.is_gt(e, rhs, lhs)) lt = true;
        else if (m.is_eq(e, lhs, rhs) && a.is_int(lhs)) eq = true;
        else return false;

        expr* t = nullptr;
        rational k;
        bool len_left;                                 // true: |t| <op> k, else k <op> |t|
        if (u.str.is_length(lhs, t) && a.is_numeral(rhs, k))
            len_left = true;
        else if (u.str.is_length(rhs, t) && a.is_numeral(lhs, k))
            len_left = false;
        else
            return false;
        if (!k.is_int() || !k.is_int64())
            return false;
        int64_t n = k.get_int64();
        if (eq)
            return !sign && tighten(t, n, n);           // |t| != k is not a bound
        int64_t s = lt ? 1 : 0;                         // strict?
        if (len_left)
            return sign ? tighten(t, n + 1 - s, INT64_MAX)   // !(|t| <= k) == |t| >= k+1
                        : tighten(t, 0, n - s);              //   |t| <= k
        return sign ? tighten(t, 0, n - 1 + s)               // !(k <= |t|) == |t| <= k-1
                    : tighten(t, n + s, INT64_MAX);          //   k <= |t|
    };

    // Collect what seq_monadic can model.  Conjunctions are traversed so that an
    // unsupported conjunct does not discard its siblings; every conjunct that cannot be
    // modelled is counted in `dropped`.  Dropping conjuncts only weakens the problem, so
    // an unsat verdict still transfers to the benchmark while a sat verdict does not.
    std::function<void(expr*)> collect = [&](expr* e) {
        expr* s = nullptr, * r = nullptr;
        if (m.is_and(e)) {
            for (expr* arg : *to_app(e))
                collect(arg);
            return;
        }
        if (!u.str.is_in_re(e, s, r)) {
            if (!collect_len(e, false))
                complete = false, ++dropped;
            return;
        }
        bool is_var = is_seq_var(s);
        if (!is_var && !u.str.is_concat(s)) {
            complete = false, ++dropped;
            return;
        }
        obj_map<expr, expr*>& map = is_var ? var_re : term_re;
        // Normalize the regex the way asserted_formulas normalizes assertions
        // before seq_regex hands them to seq_monadic. Without this the bench
        // measures raw parsed regexes, which no production path ever sees.
        expr_ref normalized(r, m);
        trw(normalized);
        pin.push_back(normalized);
        r = normalized;
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
    };
    complete = true;
    for (expr* assertion : ctx.assertions())
        collect(assertion);

    unsigned n_added = 0;
    for (expr* term : terms) {
        expr* r = nullptr;
        term_re.find(term, r);
        mon.add(term, r, nullptr);
        ++n_added;
    }
    for (auto const& [k, v] : var_re) {
        mon.add(k, v, nullptr);
        ++n_added;
    }
    for (expr* t : bounded) {
        len_bounds b;
        bounds.find(t, b);
        if (b.lo == b.hi)
            mon.add_len(t, b.lo, nullptr);
        else {
            if (b.lo > 0)
                mon.add_lo(t, b.lo, nullptr);
            if (b.hi != UINT_MAX)
                mon.add_hi(t, b.hi, nullptr);
        }
        if (b.lo > 0 || b.hi != UINT_MAX)
            ++n_added;
    }

    auto start = std::chrono::high_resolution_clock::now();
    mon.set_gen_model(false);                     // benchmark only needs the verdict
    lbool verdict = n_added == 0
        ? l_undef
        : mon.check();
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
    double solve_ms,
    unsigned dropped) {
    std::cout << file << "," << tier << "," << status << ","
              << (complete ? "yes" : "no") << "," << mode_str(mode)
              << "," << verdict_str(verdict) << "," << solve_ms
              << "," << dropped
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
        unsigned dropped = 0;
        lbool verdict = run_file(file, mode, ms, parsed, complete, dropped);
        display_row(file, "", read_status(file), complete, mode, verdict, ms, dropped);
        if (!complete)
            std::cerr << "INCOMPLETE: " << dropped << " assertion(s) not modelled; "
                      << "only an unsat verdict transfers to the benchmark\n";
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

    std::cout << "file,tier,status,complete,mode,verdict,solve_ms,dropped\n";
    unsigned agree = 0, mismatch = 0, undef = 0, unparsed = 0, incomplete = 0;
    unsigned incomplete_sat = 0;
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
        unsigned dropped = 0;
        lbool verdict = run_file(file, mode, ms, parsed, complete, dropped);
        display_row(relative, tier, status, complete, mode, verdict, ms, dropped);
        total_ms += ms;
        if (!parsed) ++unparsed;
        if (!complete) {
            ++incomplete;
            // constraints were dropped, so a sat verdict does not transfer
            if (verdict == l_true) ++incomplete_sat;
        }
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
              << " incomplete_sat=" << incomplete_sat
              << " total_solve_ms=" << total_ms << "\n";
}
