#include "cmd_context/extra_cmds/ff_integrated_cmd.h"
#include "cmd_context/extra_cmds/ff_certificate_io.h"
#include "cmd_context/parametric_cmd.h"
#include "math/ff/ff_params.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "sat/sat_extension.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include <sstream>
#include <algorithm>
#include <chrono>
#include "util/util.h"

namespace {
    struct clause_recorder : sat::clause_eh {
        ast_manager& m;
        std::vector<std::vector<sat::literal>> clauses;
        size_t size = 0;
        clause_recorder(ast_manager& m) : m(m) {}
        void on_clause(unsigned n, sat::literal const* ls, sat::status st) override {
            if (st.is_deleted()) return;
            if (!m.inc() || clauses.size() >= 100000 || n > 1000000 - size)
                throw ff::exhausted();
            size += n;
            auto& clause = clauses.emplace_back();
            for (unsigned i = 0; i < n; ++i) clause.push_back(ls[i]);
        }
    };

    struct binding {
        expr* atom;
        bool sign;
        expr* equation;
        ff::polynomial value;
        std::vector<unsigned> support;
        bool encoded = false;
    };

    // No theory fact is asserted without a recorded polynomial refutation.
    // Ordinary SAT clauses retain native DRAT evidence; the consumer replays
    // that evidence against the original CNF and independently checked lemmas.
    class proof_extension : public sat::extension {
        ast_manager& m;
        ff_certificate_io& io;
        ff::engine& normalization;
        rational prime;
        params_ref const& params;
        smt_params_helper options;
        std::unordered_map<unsigned, binding*> bindings;
        std::vector<std::pair<sat::literal, binding*>> ordered_bindings;
        std::vector<sat::literal_vector> clauses;
        std::vector<std::string> lemmas;
        size_t proof_bytes = 0;
        unsigned max_lemmas;
        std::ostream* diagnostics;
        unsigned checks = 0;
        std::vector<unsigned> minimize_order;
        std::string unknown = "no-polynomial-refutation";
    public:
        proof_extension(ast_manager& m, ff_certificate_io& io, ff::engine& normalization, rational const& p,
                        params_ref const& params, unsigned max_lemmas, std::ostream* diagnostics) :
            sat::extension(symbol("finite-field-certificates"), 0), m(m), io(io), normalization(normalization), prime(p),
            params(params), max_lemmas(max_lemmas), diagnostics(diagnostics) {}
        void bind(sat::literal l, binding& b) {
            bindings.emplace(l.index(), &b); ordered_bindings.emplace_back(l, &b);
        }
        void set_minimize_order(std::vector<unsigned> order) { minimize_order = std::move(order); }
        void add_clause(sat::literal_vector const& c) { clauses.push_back(c); }
        bool unit_propagate() override { return false; }
        bool is_external(sat::bool_var v) override {
            return bindings.contains(sat::literal(v, false).index()) || bindings.contains(sat::literal(v, true).index());
        }
        void get_antecedents(sat::literal, sat::ext_justification_idx, sat::literal_vector&, bool) override {
            // All explanations are ordinary clauses, never opaque justifications.
            throw default_exception("unexpected finite-field external justification");
        }
        void push() override {}
        void pop(unsigned) override {}
        std::ostream& display(std::ostream& out) const override { return out << "finite-field certificate extension"; }
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx) const override { return display(out); }
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx) const override { return display(out); }
        std::string reason_unknown() override { return unknown; }

        sat::check_result check() override {
            try {
                ++checks;
                if (lemmas.size() >= max_lemmas) { unknown = "field-lemma-limit"; return sat::check_result::CR_GIVEUP; }
                // A partial assignment still satisfying every original/field
                // clause suffices. Do not force irrelevant disequalities into
                // the algebra just because SAT assigned otherwise unused bits.
                std::vector<bool> keep(s().num_vars(), true);
                std::vector<unsigned> counts(clauses.size(), 0);
                std::vector<std::vector<unsigned>> supports(s().num_vars());
                for (unsigned i = 0; i < clauses.size(); ++i) {
                    if (!m.inc()) throw ff::exhausted();
                    for (auto l : clauses[i]) if (s().value(l) == l_true) {
                        ++counts[i]; supports[l.var()].push_back(i);
                    }
                    if (!counts[i]) throw default_exception("incomplete native Boolean assignment");
                }
                // Remove later declared variables first, independent of the
                // order in which clauses happened to allocate SAT variables.
                // This preserves the frontend's stable partial-model policy.
                for (unsigned v : minimize_order) {
                    bool redundant = true;
                    for (unsigned i : supports[v]) if (counts[i] <= 1) { redundant = false; break; }
                    if (redundant) {
                        keep[v] = false;
                        for (unsigned i : supports[v]) --counts[i];
                    }
                }
                std::vector<ff::polynomial> equations;
                std::vector<sat::literal> premises;
                std::vector<binding const*> selected;
                for (auto const& [l, b] : ordered_bindings) {
                    if (!keep[l.var()] || s().value(l) != l_true) continue;
                    // AST normalization depends only on the fixed declarations,
                    // not on the SAT trail. Cache it once; never cache a lemma
                    // or assumption-dependent algebraic consequence here.
                    if (!b->encoded) {
                        b->value = io.equation(b->equation, normalization);
                        b->support = io.support(b->equation); b->encoded = true;
                    }
                    selected.push_back(b); premises.push_back(l);
                }
                if (selected.empty()) return sat::check_result::CR_GIVEUP;
                // Memoization must not make variable order depend on previous
                // SAT assignments. Match a fresh frontend traversal of exactly
                // these premises, then invert this renaming on every proof term.
                std::unordered_map<expr*, unsigned> global_ids;
                for (unsigned v = 0; v < io.variables.size(); ++v) global_ids.emplace(io.variables[v], v);
                std::vector<unsigned> to_global;
                std::unordered_set<expr*> visited;
                for (auto* b : selected) {
                    expr *lhs, *rhs;
                    VERIFY(m.is_eq(b->equation, lhs, rhs));
                    ptr_vector<expr> pending;
                    pending.push_back(rhs); pending.push_back(lhs);
                    while (!pending.empty()) {
                        if (!m.inc()) throw ff::exhausted();
                        expr* t = pending.back(); pending.pop_back();
                        if (!visited.insert(t).second) continue;
                        auto it = global_ids.find(t);
                        if (it != global_ids.end()) to_global.push_back(it->second);
                        else if (is_app(t)) for (expr* arg : *to_app(t)) pending.push_back(arg);
                    }
                }
                std::vector<unsigned> to_local(io.variables.size(), ~0u);
                for (unsigned i = 0; i < to_global.size(); ++i) to_local[to_global[i]] = i;
                for (auto* b : selected) {
                    auto& f = equations.emplace_back();
                    for (auto const& [mon, coefficient] : b->value) {
                        if (!m.inc()) throw ff::exhausted();
                        auto local = mon;
                        for (auto& v : local) {
                            if (v >= to_local.size() || to_local[v] == ~0u)
                                throw default_exception("unbound field proof variable");
                            v = to_local[v];
                        }
                        std::sort(local.begin(), local.end());
                        f.emplace(std::move(local), coefficient);
                    }
                }
                ff::engine arithmetic(prime, m.limit(), params.get_uint("max_steps", 20000000),
                                      params.get_uint("max_terms", 4096), options.ff_bit_propagation(), options.ff_batch(), false);
                ff::configure_engine(arithmetic, options);
                auto started = diagnostics ? std::chrono::steady_clock::now() : std::chrono::steady_clock::time_point{};
                on_scope_exit record_stats([&]() {
                    if (!diagnostics) return;
                    auto us = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now()-started).count();
                    *diagnostics << "ff-theory check=" << checks << " lemmas=" << lemmas.size()
                                 << " equations=" << equations.size() << " variables=" << to_global.size()
                                 << " proof_us=" << us << " steps=" << arithmetic.steps() << '\n';
                    statistics stats; arithmetic.collect_statistics(stats); stats.display_smt2(*diagnostics); *diagnostics << '\n';
                });
                ff::certificate proof;
                if (!ff::certify(arithmetic, equations, proof, params.get_uint("max_nodes", 100000), ff::certificate_backend::native))
                    return sat::check_result::CR_GIVEUP;
                // All retained nodes are root ancestors. Only their actual
                // input premises justify the learned clause; no ambient SAT
                // assignment or proof from a previous check may enter its core.
                std::set<unsigned> used, required;
                for (auto const& n : proof.nodes) if (n.kind == ff::certificate::rule::input) used.insert(n.left);
                std::vector<unsigned> renumber(equations.size(), ~0u);
                std::vector<ff::polynomial> core;
                sat::literal_vector conflict;
                std::ostringstream lemma;
                lemma << "(:literals (";
                for (unsigned i : used) {
                    if (i >= equations.size()) throw default_exception("invalid native field proof input");
                    renumber[i] = core.size(); core.push_back(selected[i]->value);
                    auto l = premises[i]; conflict.push_back(~l);
                    lemma << (l.sign() ? -1 : 1) * static_cast<int>(l.var() + 1) << ' ';
                    required.insert(selected[i]->support.begin(), selected[i]->support.end());
                }
                for (auto& n : proof.nodes) {
                    if (n.kind == ff::certificate::rule::input) n.left = renumber[n.left];
                    for (auto& v : n.factor) {
                        if (v >= to_global.size()) throw default_exception("invalid field proof variable");
                        v = to_global[v];
                    }
                    std::sort(n.factor.begin(), n.factor.end());
                }
                lemma << ") :certificate "; io.display(lemma, core, proof, &required); lemma << ")\n";
                auto text = lemma.str();
                if (text.size() > 32 * 1024 * 1024 - proof_bytes) throw ff::exhausted();
                proof_bytes += text.size(); lemmas.push_back(std::move(text));
                add_clause(conflict);
                // The certified clause is globally valid. Restart from the
                // root so it can propagate before another field assignment;
                // learned Boolean clauses and every recorded lemma survive.
                s().pop_to_base_level();
                s().mk_clause(conflict, sat::status::th(false, get_id()));
                return sat::check_result::CR_CONTINUE;
            }
            catch (ff::exhausted const& ex) {
                unknown = m.limit().is_canceled() ? "canceled" : std::string("field-proof-budget/") + ex.reason;
                return sat::check_result::CR_GIVEUP;
            }
        }
        void display_lemmas(std::ostream& out) const { for (auto const& lemma : lemmas) out << lemma; }
    };

    class integrated_cmd : public parametric_cmd {
    public:
        integrated_cmd() : parametric_cmd("ff-integrated-certify") {}
        char const* get_usage() const override { return "(<keyword> <value>)*"; }
        char const* get_main_descr() const override { return "record finite-field lemmas inside native SAT search"; }
        void init_pdescrs(cmd_context&, param_descrs& d) override {
            d.insert("timeout", CPK_UINT, "whole native SAT/field proof timeout in milliseconds", "10000");
            d.insert("max_steps", CPK_UINT, "polynomial work per theory check", "20000000");
            d.insert("max_terms", CPK_UINT, "terms per polynomial", "4096");
            d.insert("max_nodes", CPK_UINT, "nodes per field certificate", "100000");
            d.insert("diagnostics", CPK_BOOL, "print field-check resource statistics to the diagnostic stream", "false");
            d.insert("max_lemmas", CPK_UINT, "field lemma count limit", "1024");
        }
        void execute(cmd_context& ctx) override {
            auto& m = ctx.m();
            cancel_eh<reslimit> cancel(m.limit()); scoped_ctrl_c interrupt(cancel);
            scoped_timer timer(m_params.get_uint("timeout", 10000), &cancel);
            try { run(ctx); }
            catch (ff::exhausted const&) { ctx.regular_stream() << "(ff-integrated-unavailable " << (m.limit().is_canceled() ? "canceled" : "budget") << ")\n"; }
            catch (z3_exception const&) {
                // Cancellation can surface from SAT/AST operations as well as
                // polynomial ticks. Keep the same incomplete-result protocol;
                // unrelated input/internal errors must still propagate.
                if (!m.limit().is_canceled()) throw;
                ctx.regular_stream() << "(ff-integrated-unavailable canceled)\n";
            }
        }
        void run(cmd_context& ctx) {
            auto& m = ctx.m(); ff_util field(m);
            std::vector<binding> bindings;
            ptr_vector<expr> assertions;
            sort* field_sort = nullptr;
            // Each registration is (= b field-equation) or
            // (= (not b) inverse-witness-equation). They are never Boolean
            // assumptions: the independent consumer supplies their input binding.
            for (expr* f : ctx.assertions()) {
                expr *atom, *eq, *a, *b;
                if (m.is_eq(f, atom, eq) && m.is_eq(eq, a, b) && field.is_ff(a)) {
                    bool sign = m.is_not(atom, atom);
                    if (!is_uninterp_const(atom) || !m.is_bool(atom)) throw cmd_exception("invalid field atom registration");
                    if (field_sort && field_sort != a->get_sort()) throw cmd_exception("integrated certificates require one field");
                    if (bindings.size() >= 8192) throw ff::exhausted();
                    field_sort = a->get_sort(); bindings.push_back({atom, sign, eq, {}, {}});
                }
                else assertions.push_back(f);
            }
            if (!field_sort) throw cmd_exception("integrated certificates require field atom registrations");
            auto const& prime = field.modulus(field_sort);
            if (prime.get_num_bits() > 4096) throw cmd_exception("certificate modulus exceeds the profile");
            ff::engine normalization(prime, m.limit(), m_params.get_uint("max_steps", 20000000), m_params.get_uint("max_terms", 4096));
            ff_certificate_io io(ctx, field_sort, 2000000);
            clause_recorder recorder(m);
            params_ref params;
            // This command exports a single CDCL trace. Alternative stochastic
            // engines do not supply the theory callbacks/proof protocol here.
            params.set_bool("local_search", false);
            params.set_bool("ddfw_search", false);
            params.set_bool("prob_search", false);
            params.set_uint("threads", 1);
            sat::solver solver(params, m.limit());
            // One command owns the entire state. Push/pop/reset between commands
            // cannot leave stale learned clauses, AST references, or certificates.
            solver.set_incremental(true); solver.set_drat(true); solver.get_drat().set_clause_eh(recorder);
            auto* extension = alloc(proof_extension, m, io, normalization, prime, m_params, std::min(1024u, m_params.get_uint("max_lemmas", 1024)), m_params.get_bool("diagnostics", false) ? &ctx.diagnostic_stream() : nullptr);
            solver.set_extension(extension); // solver owns the extension
            std::unordered_map<expr*, sat::literal> literals;
            ptr_vector<expr> names;
            std::vector<unsigned> exported(solver.num_vars(), ~0u);
            for (expr* assertion : assertions) {
                ptr_vector<expr> terms;
                if (m.is_or(assertion)) for (expr* a : *to_app(assertion)) terms.push_back(a);
                else if (!m.is_false(assertion)) terms.push_back(assertion);
                sat::literal_vector clause;
                for (expr* term : terms) {
                    bool sign = false; expr* child;
                    while (m.is_not(term, child)) { term = child; sign = !sign; }
                    if (!is_uninterp_const(term) || !m.is_bool(term)) throw cmd_exception("integrated certificates require Boolean CNF");
                    auto it = literals.find(term);
                    if (it == literals.end()) {
                        if (names.size() >= 100000) throw ff::exhausted();
                        auto l = sat::literal(solver.mk_var(true), false);
                        it = literals.emplace(term, l).first;
                        exported.resize(solver.num_vars(), ~0u); exported[l.var()] = names.size() + 1; names.push_back(term);
                    }
                    clause.push_back(sign ? ~it->second : it->second);
                }
                extension->add_clause(clause); solver.mk_clause(clause);
            }
            std::unordered_set<unsigned> registered;
            for (auto& b : bindings) {
                auto it = literals.find(b.atom);
                if (it == literals.end()) continue;
                auto l = b.sign ? ~it->second : it->second;
                if (!registered.insert(l.index()).second) throw cmd_exception("duplicate field atom registration");
                extension->bind(l, b);
            }
            std::vector<std::pair<unsigned, unsigned>> order;
            for (auto const& [atom, lit] : literals) order.emplace_back(to_app(atom)->get_decl()->get_id(), lit.var());
            std::sort(order.rbegin(), order.rend());
            std::vector<unsigned> minimize_order;
            for (auto const& [id, v] : order) minimize_order.push_back(v);
            extension->set_minimize_order(std::move(minimize_order));
            // An input empty clause can leave no SAT trail. It already closes
            // the input CNF; avoid asking DRAT conflict analysis to walk an empty
            // trail. The consumer still independently replays this contradiction.
            auto result = solver.inconsistent() ? l_false : solver.check();
            if (result != l_false) {
                ctx.regular_stream() << "(ff-integrated-unavailable " << (m.limit().is_canceled() ? "canceled" : extension->reason_unknown()) << ")\n";
                return;
            }
            std::ostringstream out;
            out << "(ff-integrated-result :status unsat :variables (";
            // Preserve SAT variable numbering, including any unused leading slot.
            for (unsigned v = 0; v < exported.size(); ++v) {
                if (exported[v] == ~0u) out << "_ ";
                else { ctx.display(out, names[exported[v] - 1]); out << ' '; }
            }
            out << ") :lemmas ("; extension->display_lemmas(out); out << ") :clauses (";
            for (auto const& clause : recorder.clauses) {
                if (!m.inc() || out.tellp() > 32 * 1024 * 1024) throw ff::exhausted();
                out << '(';
                for (auto l : clause) {
                    if (l.var() >= exported.size() || exported[l.var()] == ~0u) throw cmd_exception("unbound native SAT proof variable");
                    out << (l.sign() ? -1 : 1) * static_cast<int>(l.var() + 1) << ' ';
                }
                out << ')';
            }
            out << "))\n";
            if (out.tellp() > 32 * 1024 * 1024) throw ff::exhausted();
            ctx.regular_stream() << out.str();
        }
    };
}
void install_ff_integrated_cmd(cmd_context& ctx) { ctx.insert(alloc(integrated_cmd)); }
