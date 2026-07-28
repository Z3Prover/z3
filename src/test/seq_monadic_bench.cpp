/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_monadic_bench.cpp

Abstract:

    Benchmark harness for the whole-language monadic-decomposition membership solver
    (ast/rewriter/seq_monadic).  Reads every *.smt2 under the directory named by the
    environment variable Z3_SEQ_BENCH_DIR, extracts the regex-membership constraints
    (mirroring the c3 theory_nseq run_monadic_diagnostic two-pass grouping: per-variable
    base memberships -> var_extra, compound-term memberships -> intersect per term), runs
    seq_monadic::solve on each with wall-clock timing, and prints a CSV plus a summary
    comparing the verdict against the file's authoritative (set-info :status).

    Not run by `test-z3 /a` (it is a no-op unless Z3_SEQ_BENCH_DIR is set).  Invoke with:
        $env:Z3_SEQ_BENCH_DIR="C:\git\bench\inputs\regexes\MargusRegex"; test-z3 seq_monadic_bench

Author:

    Nikolaj Bjorner / Margus Veanes 2026

--*/

#define _CRT_SECURE_NO_WARNINGS   // getenv is fine for this dev-only harness

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

    char const* verdict_str(lbool l) { return l == l_true ? "sat" : l == l_false ? "unsat" : "undef"; }

    // conjunction of per-term verdicts: unsat dominates, then undef, else sat.
    bool is_seq_var(ast_manager& m, expr* t) {
        return is_app(t) && to_app(t)->get_num_args() == 0 &&
               to_app(t)->get_family_id() == null_family_id;
    }

    std::string read_status(std::string const& path) {
        std::ifstream in(path);
        std::stringstream ss; ss << in.rdbuf();
        std::string txt = ss.str();
        std::smatch mm;
        std::regex re("set-info\\s*:status\\s+(sat|unsat|unknown)");
        if (std::regex_search(txt, mm, re)) return mm[1].str();
        return "?";   // no authoritative status (do NOT guess from the filename)
    }

    // Parse one file, extract memberships, run seq_monadic; returns verdict, sets solve_ms.
    lbool run_file(std::string const& path, double& solve_ms, bool& parsed) {
        solve_ms = 0; parsed = false;
        cmd_context ctx(false);                  // ctx owns + initializes the manager (plugins)
        ctx.set_ignore_check(true);
        {
            std::ifstream is(path);
            if (!is.good()) return l_undef;
            if (!parse_smt2_commands(ctx, is)) return l_undef;
        }
        parsed = true;
        ast_manager& m = ctx.m();
        seq_util u(m);
        seq_rewriter rw(m);
        seq_monadic mon(rw);

        obj_map<expr, expr*> var_extra;   // variable -> intersected base regex
        obj_map<expr, expr*> term_re;     // compound term -> intersected regex
        ptr_vector<expr> terms;
        expr_ref_vector pin(m);

        std::function<void(expr*)> collect = [&](expr* a) {
            expr* s = nullptr, * r = nullptr;
            if (m.is_and(a)) { for (expr* arg : *to_app(a)) collect(arg); return; }
            if (!u.str.is_in_re(a, s, r)) return;
            if (is_seq_var(m, s)) {
                expr* prev = nullptr;
                if (var_extra.find(s, prev)) {
                    expr_ref in = rw.mk_regex_inter_normalize(prev, r);
                    pin.push_back(in); var_extra.insert(s, in);
                }
                else var_extra.insert(s, r);
            }
            else if (u.str.is_concat(s)) {
                expr* prev = nullptr;
                if (term_re.find(s, prev)) {
                    expr_ref in = rw.mk_regex_inter_normalize(prev, r);
                    pin.push_back(in); term_re.insert(s, in);
                }
                else { term_re.insert(s, r); terms.push_back(s); }
            }
            // ground / unsupported term shapes are ignored
        };
        for (expr* a : ctx.assertions()) collect(a);

        // The whole file is a CONJUNCTION of its memberships; solve them jointly (bare-
        // variable base memberships included) so a variable shared across memberships is
        // constrained consistently -- independent per-term solving is unsound there.
        vector<std::pair<expr*, expr*>> mems;
        for (expr* t : terms) { expr* R = nullptr; term_re.find(t, R); mems.push_back(std::make_pair(t, R)); }
        for (auto const& kv : var_extra) mems.push_back(std::make_pair(kv.m_key, kv.m_value));

        obj_map<expr, expr*> empty_extra;
        auto t0 = std::chrono::high_resolution_clock::now();
        lbool verdict = mems.empty() ? l_undef : mon.solve_and(mems, empty_extra);
        solve_ms = std::chrono::duration<double, std::milli>(
            std::chrono::high_resolution_clock::now() - t0).count();
        return verdict;
    }

}

void tst_seq_monadic_bench() {
    namespace fs = std::filesystem;
    std::error_code ec;

    // Single-file mode (for crash-isolated batch driving): process exactly one file and
    // print one CSV line  file,status,verdict,solve_ms  (no header, no summary).  A crash
    // on a pathological file then only kills this one child process.
    if (const char* one = getenv("Z3_SEQ_BENCH_FILE")) {
        double ms = 0; bool parsed = false;
        lbool v = run_file(one, ms, parsed);
        std::cout << one << "," << read_status(one) << "," << verdict_str(v) << "," << ms << "\n" << std::flush;
        return;
    }

    const char* dir = getenv("Z3_SEQ_BENCH_DIR");
    if (!dir) {
        std::cout << "seq_monadic_bench: set Z3_SEQ_BENCH_DIR to a directory of .smt2 files to run.\n";
        return;
    }
    if (!fs::exists(dir, ec)) { std::cout << "seq_monadic_bench: dir not found: " << dir << "\n"; return; }

    std::vector<std::string> files;
    for (auto& e : fs::recursive_directory_iterator(dir, ec))
        if (e.is_regular_file() && e.path().extension() == ".smt2")
            files.push_back(e.path().string());
    std::sort(files.begin(), files.end());

    std::cout << "file,tier,status,verdict,solve_ms\n";
    unsigned nfiles = 0, agree = 0, mismatch = 0, undef = 0, unparsed = 0;
    double total_ms = 0, max_ms = 0;
    std::string max_file;
    for (auto const& f : files) {
        std::string status = read_status(f);
        std::string rel = fs::relative(f, dir, ec).generic_string();
        std::cerr << "[" << (nfiles + 1) << "/" << files.size() << "] " << rel << std::endl;
        double ms = 0; bool parsed = false;
        lbool v = run_file(f, ms, parsed);
        std::string vs = verdict_str(v);
        std::string tier = rel.substr(0, rel.find('/'));
        std::cout << rel << "," << tier << "," << status << "," << vs << "," << ms << "\n" << std::flush;
        ++nfiles; total_ms += ms;
        if (ms > max_ms) { max_ms = ms; max_file = rel; }
        if (!parsed) ++unparsed;
        if (v == l_undef) ++undef;
        else if (status == "sat" || status == "unsat") { if (vs == status) ++agree; else ++mismatch; }
    }
    unsigned decided = agree + mismatch;
    std::cout << "# SUMMARY files=" << nfiles
              << " decided=" << decided << " (agree=" << agree << " mismatch=" << mismatch << ")"
              << " undef=" << undef << " unparsed=" << unparsed
              << " total_solve_ms=" << total_ms
              << " max_solve_ms=" << max_ms << " (" << max_file << ")\n";
}
