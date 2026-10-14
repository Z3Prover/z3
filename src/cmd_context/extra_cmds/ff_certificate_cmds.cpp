/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_certificate_cmds.cpp

Abstract:

    ff-certify command: reconstructs and prints a standalone polynomial
    ideal-membership certificate (see ff_certificate.h) from the field
    equations currently asserted in the command context.

Author:

    Romain Soulat

--*/
#include "cmd_context/cmd_context.h"
#include "cmd_context/extra_cmds/ff_certificate_io.h"
#include "cmd_context/extra_cmds/ff_integrated_cmd.h"
#include "cmd_context/parametric_cmd.h"
#include "ast/ff_decl_plugin.h"
#include "math/ff/ff_certificate.h"
#include "math/ff/ff_params.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include <sstream>
#include <memory>
#include <unordered_map>

namespace {
    // Native SAT evidence for the Boolean layer. The caller independently binds
    // these clauses to its input and field lemmas; this command trusts neither
    // their origin nor a solver result as a certificate of the original formula.
    class ff_boolean_certify_cmd : public parametric_cmd {
        struct recorder : sat::clause_eh {
            ast_manager &m;
            std::vector<std::vector<int>> clauses;
            size_t literals = 0;
            recorder(ast_manager &m) : m(m) {}
            void on_clause(unsigned n, sat::literal const *ls, sat::status st) override {
                if (st.is_deleted()) return;
                if (!m.inc() || clauses.size() >= 100000 || n > 1000000 - literals)
                    throw default_exception("native Boolean proof budget");
                literals += n;
                auto &c = clauses.emplace_back();
                for (unsigned i = 0; i < n; ++i)
                    c.push_back((ls[i].sign() ? -1 : 1) * static_cast<int>(ls[i].var() + 1));
            }
        };
        struct state {
            // Destruction order matters: SAT callbacks must not outlive trace.
            recorder trace;
            params_ref params;
            sat::solver solver;
            expr_ref_vector assertions, names;
            std::unordered_map<expr*, sat::literal> literals;
            std::vector<unsigned> exported;
            state(ast_manager &m, bool incremental) : trace(m), solver(params, m.limit()), assertions(m), names(m),
                                    exported(solver.num_vars(), ~0u) {
                solver.set_incremental(incremental);
                solver.set_drat(true);
                solver.get_drat().set_clause_eh(trace);
            }
        };
        std::unique_ptr<state> m_state;
    public:
        ff_boolean_certify_cmd() : parametric_cmd("ff-boolean-certify") {}
        void reset(cmd_context &) override { m_state.reset(); }
        void finalize(cmd_context &) override { m_state.reset(); }
        char const *get_usage() const override { return "(<keyword> <value>)*"; }
        char const *get_main_descr() const override { return "solve Boolean CNF and record native SAT clause evidence"; }
        void init_pdescrs(cmd_context &, param_descrs &d) override {
            d.insert("timeout", CPK_UINT, "native Boolean proof timeout in milliseconds", "10000");
            d.insert("incremental", CPK_BOOL, "retain native SAT and proof state across monotone assertion additions", "false");
        }
        void execute(cmd_context &ctx) override {
            auto &m = ctx.m();
            cancel_eh<reslimit> cancel(m.limit());
            scoped_ctrl_c interrupt(cancel);
            scoped_timer timer(m_params.get_uint("timeout", 10000), &cancel);
            bool incremental = m_params.get_bool("incremental", false);
            try { run(ctx, incremental); }
            catch (...) { m_state.reset(); throw; }
            if (!incremental) m_state.reset();
        }
        void run(cmd_context &ctx, bool incremental) {
            auto &m = ctx.m();
            auto const &current = ctx.assertions();
            // Learned clauses remain justified only when every old assertion is
            // still active. Pop/replacement/reset rebuilds both search and trace;
            // a dependency list alone never authorizes reusing a stale lemma.
            bool reuse = incremental && m_state && current.size() >= m_state->assertions.size();
            if (reuse) for (unsigned i = 0; i < m_state->assertions.size(); ++i)
                if (current[i] != m_state->assertions[i]) { reuse = false; break; }
            if (!reuse) m_state = std::make_unique<state>(m, incremental);
            auto &s = *m_state;
            auto &solver = s.solver;
            auto &literals = s.literals;
            auto &names = s.names;
            auto &exported = s.exported;
            solver.pop_to_base_level();
            for (unsigned i = s.assertions.size(); i < current.size(); ++i) {
                expr *assertion = current[i];
                sat::literal_vector clause;
                ptr_vector<expr> terms;
                if (m.is_or(assertion)) for (expr *arg : *to_app(assertion)) terms.push_back(arg);
                else if (!m.is_false(assertion)) terms.push_back(assertion);
                for (expr *term : terms) {
                    bool neg = false;
                    expr *child;
                    while (m.is_not(term, child)) { term = child; neg = !neg; }
                    if (!is_uninterp_const(term) || !m.is_bool(term))
                        throw cmd_exception("ff-boolean-certify requires clauses of Boolean constants");
                    auto it = literals.find(term);
                    if (it == literals.end()) {
                        if (names.size() >= 100000) throw cmd_exception("native Boolean variable limit");
                        sat::literal lit(solver.mk_var(true), false);
                        it = literals.emplace(term, lit).first;
                        exported.resize(solver.num_vars(), ~0u);
                        exported[lit.var()] = names.size() + 1;
                        names.push_back(term);
                    }
                    clause.push_back(neg ? ~it->second : it->second);
                }
                solver.mk_clause(clause);
                s.assertions.push_back(assertion);
            }
            auto result = solver.check();
            std::ostringstream out;
            out << "(ff-boolean-result :status " << (result == l_true ? "sat" : result == l_false ? "unsat" : "unknown");
            out << " :variables (";
            for (auto *name : names) { ctx.display(out, name); out << ' '; }
            out << ") :model (";
            if (result == l_true) {
                auto const &model = solver.get_model();
                for (auto *name : names) out << (model[literals.at(name).var()] == l_true ? "true " : "false ");
            }
            out << ") :clauses (";
            // The complete retained trace includes learned clauses from earlier
            // SAT checks. The receiver replays these against its bound premises;
            // input-labelled clauses are never new trusted assumptions.
            if (result == l_false) for (auto const &clause : s.trace.clauses) {
                out << '(';
                for (int lit : clause) {
                    unsigned v = static_cast<unsigned>(lit < 0 ? -lit : lit) - 1;
                    if (v >= exported.size() || exported[v] == ~0u)
                        throw cmd_exception("native SAT evidence contains an unbound auxiliary");
                    out << (lit < 0 ? -static_cast<int>(exported[v]) : static_cast<int>(exported[v])) << ' ';
                }
                out << ')';
            }
            out << "))\n";
            ctx.regular_stream() << out.str();
            ctx.regular_stream().flush();
            if (result == l_undef) m_state.reset();
        }
    };

    class ff_certify_cmd : public parametric_cmd {
    public:
        ff_certify_cmd() : parametric_cmd("ff-certify") {}
        char const *get_usage() const override { return "(<keyword> <value>)*"; }
        char const *get_main_descr() const override {
            return "reconstruct a standalone polynomial contradiction from current field equations";
        }
        void init_pdescrs(cmd_context &, param_descrs &d) override {
            d.insert("backend", CPK_SYMBOL, "certificate search: auto, scalar, f4 or native", "auto");
            d.insert("unique", CPK_BOOL, "record shared native affine uniqueness propagation", "true");
            d.insert("branches", CPK_BOOL, "record and discharge shared native Boolean-domain branches", "true");
            d.insert("max_steps", CPK_UINT, "maximum polynomial operations", "2000000");
            d.insert("max_terms", CPK_UINT, "maximum terms per polynomial", "4096");
            d.insert("max_nodes", CPK_UINT, "maximum derivation DAG nodes", "100000");
            d.insert("timeout", CPK_UINT, "certificate reconstruction timeout in milliseconds", "10000");
        }
        void execute(cmd_context &ctx) override {
            ast_manager &m = ctx.m();
            ff_util field(m);
            cancel_eh<reslimit> cancel(m.limit());
            scoped_ctrl_c interrupt(cancel);
            scoped_timer timer(m_params.get_uint("timeout", 10000), &cancel);
            try {
                // Read assertions directly: no unsupported preprocessing can
                // become an implicit assumption of the exported certificate.
                ptr_vector<expr> todo, literals;
                for (expr *f : ctx.assertions()) todo.push_back(f);
                std::reverse(todo.begin(), todo.end());
                sort *s = nullptr;
                while (!todo.empty()) {
                    if (!m.inc()) throw ff::exhausted();
                    expr *f = todo.back(); todo.pop_back();
                    if (m.is_and(f)) {
                        app *a = to_app(f);
                        for (unsigned i = a->get_num_args(); i-- > 0;) todo.push_back(a->get_arg(i));
                        continue;
                    }
                    expr *a, *b;
                    if (!m.is_eq(f, a, b) || !field.is_ff(a))
                        throw cmd_exception("ff-certify supports only conjunctions of field equalities");
                    if (s && s != a->get_sort())
                        throw cmd_exception("ff-certify requires one field per certificate");
                    s = a->get_sort();
                    if (literals.size() >= 4096) throw ff::exhausted();
                    literals.push_back(f);
                }
                if (!s) throw cmd_exception("ff-certify requires field equations");
                auto const &prime = field.modulus(s);
                if (prime.get_num_bits() > 4096)
                    throw cmd_exception("ff-certify modulus exceeds the certificate profile");
                symbol backend_name = m_params.get_sym("backend", symbol("auto"));
                auto backend = ff::certificate_backend::automatic;
                if (backend_name == "scalar") backend = ff::certificate_backend::scalar;
                else if (backend_name == "f4") backend = ff::certificate_backend::f4;
                else if (backend_name == "native") backend = ff::certificate_backend::native;
                else if (backend_name != "auto") throw cmd_exception("ff-certify: expected backend auto, scalar, f4 or native");
                bool native = backend == ff::certificate_backend::native;
                smt_params_helper options;
                ff::engine arithmetic(prime, m.limit(), m_params.get_uint("max_steps", 2000000),
                                      m_params.get_uint("max_terms", 4096),
                                      native && options.ff_bit_propagation(), native && options.ff_batch(), false);
                if (native) ff::configure_engine(arithmetic, options);
                ff_certificate_io io(ctx, s);
                std::vector<ff::polynomial> equations;
                for (expr* literal : literals) equations.push_back(io.equation(literal, arithmetic));
                ff::certificate proof;
                if (!ff::certify(arithmetic, equations, proof, m_params.get_uint("max_nodes", 100000), backend, m_params.get_bool("unique", true), m_params.get_bool("branches", true))) {
                    ctx.regular_stream() << "(ff-certificate-unavailable no-polynomial-refutation)\n";
                    return;
                }
                // Buffer the entire object so cancellation cannot leave a
                // truncated object that looks like a successful certificate.
                std::ostringstream out;
                io.display(out, equations, proof);
                ctx.regular_stream() << out.str();
            }
            catch (ff::exhausted const &) {
                ctx.regular_stream() << "(ff-certificate-unavailable budget)\n";
            }
        }
    };
}
void install_ff_certificate_cmds(cmd_context &ctx) { ctx.insert(alloc(ff_certify_cmd)); ctx.insert(alloc(ff_boolean_certify_cmd)); install_ff_integrated_cmd(ctx); }
