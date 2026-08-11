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

char const* mode_str(seq::transition_mode mode) {
    switch (mode) {
    case seq::transition_mode::brzozowski_tm: return "brz";
    case seq::transition_mode::light_antimirov_tm: return "light-ant";
    }
    UNREACHABLE();
    return "";
}

seq::transition_mode get_mode() {
    char const* mode = getenv("Z3_SEQ_MONADIC_MODE");
    if (mode && std::string(mode) == "brz")
        return seq::transition_mode::brzozowski_tm;
    return seq::transition_mode::light_antimirov_tm;
}

// Mirrors the seq.regex_budget parameter so the bench can sweep the budget in isolation.
unsigned get_budget() {
    char const* budget = getenv("Z3_SEQ_MONADIC_BUDGET");
    if (budget)
        return static_cast<unsigned>(strtoul(budget, nullptr, 10));
    return 1000000;
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
    seq::transition_mode mode,
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
    mon.set_budget(get_budget());

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

    // A length equation |t| = c*k + d, where k is an integer variable occurring in no
    // other assertion than its own bounds, describes exactly the lengths congruent to d
    // modulo c that those bounds allow -- that is, t in .{base}(.{c})*.  seq_monadic has
    // no integer reasoning, so without this rewrite both the equation and its guard are
    // dropped and the benchmark measures a strictly weaker problem.
    obj_map<expr, expr*> modular_re;         // the equation  -> regex encoding it
    obj_map<expr, expr*> modular_term;       // the equation  -> the string term
    obj_hashtable<expr> consumed;            // guards fully accounted for by the encoding
    {
        ptr_vector<expr> conjuncts;
        std::function<void(expr*)> flatten = [&](expr* e) {
            if (m.is_and(e))
                for (expr* arg : *to_app(e))
                    flatten(arg);
            else
                conjuncts.push_back(e);
        };
        for (expr* assertion : ctx.assertions())
            flatten(assertion);

        auto is_int_var = [&](expr* e) { return is_uninterp_const(e) && a.is_int(e); };

        auto occurs = [&](expr* e, expr* k) {
            obj_hashtable<expr> seen;
            ptr_vector<expr> todo;
            todo.push_back(e);
            while (!todo.empty()) {
                expr* t = todo.back();
                todo.pop_back();
                if (t == k)
                    return true;
                if (!is_app(t) || seen.contains(t))
                    continue;
                seen.insert(t);
                for (expr* arg : *to_app(t))
                    todo.push_back(arg);
            }
            return false;
        };

        // c*k + d, with a single integer variable k and c > 0
        auto parse_linear = [&](expr* e, expr*& k, rational& c, rational& d) {
            k = nullptr;
            c.reset();
            d.reset();
            ptr_vector<expr> todo;
            todo.push_back(e);
            rational v;
            while (!todo.empty()) {
                expr* t = todo.back();
                todo.pop_back();
                expr* x = nullptr, * y = nullptr;
                if (a.is_add(t))
                    for (expr* arg : *to_app(t))
                        todo.push_back(arg);
                else if (a.is_numeral(t, v))
                    d += v;
                else if (a.is_mul(t, x, y) && a.is_numeral(x, v) && is_int_var(y)) {
                    if (k && k != y)
                        return false;
                    k = y, c += v;
                }
                else if (is_int_var(t)) {
                    if (k && k != t)
                        return false;
                    k = t, c += rational(1);
                }
                else
                    return false;
            }
            return k != nullptr && c.is_pos();
        };

        // k <= v / v <= k, including the strict and reversed spellings
        auto parse_guard = [&](expr* e, expr*& k, bool& is_lower, rational& bound) {
            expr* lhs = nullptr, * rhs = nullptr;
            bool strict = false;
            if (a.is_le(e, lhs, rhs)) {}
            else if (a.is_lt(e, lhs, rhs)) strict = true;
            else if (a.is_ge(e, rhs, lhs)) {}
            else if (a.is_gt(e, rhs, lhs)) strict = true;
            else return false;
            rational v;
            if (is_int_var(lhs) && a.is_numeral(rhs, v)) {
                k = lhs; is_lower = false; bound = strict ? v - 1 : v; return true;
            }
            if (a.is_numeral(lhs, v) && is_int_var(rhs)) {
                k = rhs; is_lower = true; bound = strict ? v + 1 : v; return true;
            }
            return false;
        };

        auto fits = [&](rational const& r) {
            if (!r.is_int() || !r.is_int64())
                return false;
            int64_t v = r.get_int64();
            return -(int64_t)MAX_LEN_BOUND <= v && v <= (int64_t)MAX_LEN_BOUND;
        };

        for (expr* eq : conjuncts) {
            expr* lhs = nullptr, * rhs = nullptr, * t = nullptr, * k = nullptr;
            rational c, d;
            if (!m.is_eq(eq, lhs, rhs) || !a.is_int(lhs))
                continue;
            if (!(u.str.is_length(lhs, t) && parse_linear(rhs, k, c, d)) &&
                !(u.str.is_length(rhs, t) && parse_linear(lhs, k, c, d)))
                continue;
            if (!is_seq_var(t) && !u.str.is_concat(t))
                continue;
            if (!fits(c) || !fits(d))
                continue;

            // Every other assertion mentioning k has to be a bound on k alone, otherwise
            // eliminating k would lose information.
            ptr_vector<expr> guards;
            bool has_lo = false, has_hi = false, ok = true;
            rational lo, hi;
            for (expr* other : conjuncts) {
                if (other == eq || !occurs(other, k))
                    continue;
                expr* gk = nullptr;
                bool is_lower = false;
                rational bound;
                if (!parse_guard(other, gk, is_lower, bound) || gk != k || !fits(bound)) {
                    ok = false;
                    break;
                }
                if (is_lower) {
                    lo = has_lo ? std::max(lo, bound) : bound;
                    has_lo = true;
                } else {
                    hi = has_hi ? std::min(hi, bound) : bound;
                    has_hi = true;
                }
                guards.push_back(other);
            }
            if (!ok)
                continue;

            int64_t ci = c.get_int64(), di = d.get_int64();
            int64_t base = ((di % ci) + ci) % ci;        // least non-negative length = d (mod c)
            if (has_lo) {
                // c*lo + d is congruent to base modulo c, so it is reached exactly.
                int64_t lowest = ci * lo.get_int64() + di;
                if (lowest > base)
                    base = lowest;
            }
            int64_t periods = -1;                        // -1: unbounded, i.e. a star
            if (has_hi) {
                int64_t highest = ci * hi.get_int64() + di;
                if (highest < base)
                    continue;                            // empty; not worth encoding
                periods = (highest - base) / ci;
            }
            if (base > MAX_LEN_BOUND || periods > MAX_LEN_BOUND)
                continue;

            sort* re_sort = u.re.mk_re(t->get_sort());
            expr_ref all_char(u.re.mk_full_char(re_sort), m);
            expr_ref period(u.re.mk_loop_proper(all_char, (unsigned)ci, (unsigned)ci), m);
            expr_ref rep(m);
            if (periods < 0)
                rep = u.re.mk_star(period);
            else
                rep = u.re.mk_loop_proper(period, 0, (unsigned)periods);
            expr_ref regex(rep, m);
            if (base > 0) {
                expr_ref prefix(u.re.mk_loop_proper(all_char, (unsigned)base, (unsigned)base), m);
                regex = u.re.mk_concat(prefix, rep);
            }
            pin.push_back(regex);
            modular_re.insert(eq, regex);
            modular_term.insert(eq, t);
            for (expr* g : guards)
                consumed.insert(g);
        }
    }

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
        // A negated membership is a membership in the complement.  seq_monadic handles
        // re.comp natively and seq_regex::unfold_complement performs the same rewrite on
        // the production path, so modelling it here rather than dropping it keeps the
        // benchmark faithful to what the solver actually sees.
        bool negated = false;
        expr* arg = nullptr;
        if (consumed.contains(e))
            return;                          // a guard the modular encoding folded in
        if (modular_re.find(e, r))
            modular_term.find(e, s);
        else if (m.is_not(e, arg) && u.str.is_in_re(arg, s, r))
            negated = true;
        else if (!u.str.is_in_re(e, s, r)) {
            if (!collect_len(e, false)) {
                complete = false;
                ++dropped;
            }
            return;
        }
        bool is_var = is_seq_var(s);
        if (!is_var && !u.str.is_concat(s)) {
            complete = false;
            ++dropped;
            return;
        }
        obj_map<expr, expr*>& map = is_var ? var_re : term_re;
        // Normalize the regex the way asserted_formulas normalizes assertions
        // before seq_regex hands them to seq_monadic. Without this the bench
        // measures raw parsed regexes, which no production path ever sees.
        expr_ref normalized(negated ? u.re.mk_complement(r) : r, m);
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
    seq::transition_mode mode,
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
    seq::transition_mode mode = get_mode();

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
