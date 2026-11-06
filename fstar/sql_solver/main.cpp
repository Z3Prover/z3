#include <z3++.h>
extern "C" {
#include "SqlCherry.h"
}
#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace sql {
struct bridge;
static thread_local bridge* active = nullptr;

struct bridge {
    z3::context& ctx;
    std::unordered_map<std::string, z3::sort> sorts;
    std::vector<z3::func_decl> declarations;
    std::unordered_map<unsigned, unsigned> opcodes;
    std::unordered_map<unsigned, z3::func_decl> constructors;
    std::unordered_map<uint64_t, z3::expr> pinned;

    explicit bridge(z3::context& c) : ctx(c) {
        sorts.emplace("Int", ctx.int_sort());
        sorts.emplace("String", ctx.string_sort());
    }
    z3::expr pin(z3::expr const& e) {
        pinned.emplace(e.id(), e);
        return e;
    }
    void add_sort(char const* name) { sorts.emplace(name, ctx.uninterpreted_sort(name)); }
    void declare(char const* name, unsigned code,
                 std::initializer_list<char const*> domain, char const* range) {
        std::vector<Z3_sort> arguments;
        for (auto s : domain) arguments.push_back(sorts.at(s));
        z3::func_decl f(ctx, Z3_solver_propagate_declare(
            ctx, ctx.str_symbol(name), static_cast<unsigned>(arguments.size()),
            arguments.data(), sorts.at(range)));
        declarations.push_back(f);
        opcodes.emplace(f.id(), code);
        if (code != 0 && code != 21 && code != 32) constructors.emplace(code, f);
    }
    unsigned opcode(z3::expr const& e) const {
        if (!e.is_app()) return 0;
        auto it = opcodes.find(e.decl().id());
        return it == opcodes.end() ? 0 : it->second;
    }
    z3::expr make(unsigned op, std::initializer_list<Z3_ast> arguments) {
        z3::expr_vector args(ctx);
        for (auto arg : arguments) args.push_back(z3::expr(ctx, arg));
        return pin(constructors.at(op)(args));
    }
    z3::expr_vector parse(std::string const& text) {
        std::vector<Z3_symbol> sn, fn;
        std::vector<Z3_sort> ss;
        std::vector<Z3_func_decl> fs;
        for (auto const& [name, sort] : sorts) {
            if (name == "Int" || name == "String") continue;
            sn.push_back(ctx.str_symbol(name.c_str()));
            ss.push_back(sort);
        }
        for (auto const& f : declarations) {
            fn.push_back(f.name());
            fs.push_back(f);
        }
        Z3_ast_vector result = Z3_parse_smtlib2_string(
            ctx, text.c_str(), static_cast<unsigned>(sn.size()), sn.data(), ss.data(),
            static_cast<unsigned>(fn.size()), fn.data(), fs.data());
        ctx.check_error();
        return z3::expr_vector(ctx, result);
    }
};

#include "signature.inc"

class propagator : public z3::user_propagator_base {
    z3::solver& solver;
    bridge& native;
    std::vector<z3::expr> terms;
    std::vector<z3::expr> applications;
    std::unordered_set<unsigned> observed, emitted;
    unsigned limit;
    unsigned depth = 0;

    bool consequence(z3::expr const& lemma, bool rewrite, bool graph) {
        native.pin(lemma);
        if (emitted.count(lemma.id())) return false;
        if (emitted.size() >= limit) { incomplete = true; return false; }
        emitted.insert(lemma.id());
        z3::expr_vector premises(ctx());
        bool progress = propagate(premises, lemma);
        if (progress) {
            if (rewrite) {
                ++rewrites;
                if (graph) ++egraph_rewrites;
            }
            else ++congruences;
        }
        return progress;
    }
    bool functional_congruence() {
        // User-propagator declarations suppress Z3's ordinary argument congruence.
        std::unordered_map<std::string, z3::expr> classes;
        auto count = applications.size();
        for (size_t j = 0; j < count; ++j) {
            z3::expr t = applications[j];
            std::string key = std::to_string(t.decl().id());
            for (unsigned k = 0; k < t.num_args(); ++k)
                key += ":" + std::to_string(solver.congruence_root(t.arg(k)).id());
            auto [entry, inserted] = classes.emplace(key, t);
            if (inserted) continue;
            z3::expr other = entry->second;
            if (z3::eq(solver.congruence_root(t), solver.congruence_root(other))) continue;
            z3::expr guard = ctx().bool_val(true);
            for (unsigned k = 0; k < t.num_args(); ++k)
                guard = guard && (t.arg(k) == other.arg(k));
            if (consequence(z3::implies(guard, t == other), false, false)) return true;
            if (incomplete) return false;
        }
        return false;
    }
    bool bounded_tree(z3::expr const& t, unsigned fuel, unsigned& budget) {
        if (budget == 0) return false;
        --budget;
        if (!t.is_app() || fuel == 0) return true;
        for (unsigned j = 0; j < t.num_args(); ++j)
            if (!bounded_tree(t.arg(j), fuel - 1, budget)) return false;
        return true;
    }
    bool emit(z3::expr const& source, z3::expr const& variant,
              z3::expr const* guard = nullptr) {
        unsigned budget = 8192;
        if (!bounded_tree(variant, 32, budget)) { incomplete = true; return false; }
        active = &native;
        z3::expr target(native.ctx, Sql_Cherry_rewrite_native(variant));
        native.pin(target);
        if (z3::eq(variant, target) || z3::eq(source, target)) return false;
        z3::expr lemma = source == target;
        if (guard) lemma = z3::implies(*guard, lemma);
        return consequence(lemma, true, guard != nullptr);
    }
public:
    uint64_t finals = 0, rewrites = 0, egraph_rewrites = 0, creations = 0, equalities = 0, congruences = 0;
    bool incomplete = false;
    propagator(z3::solver& s, bridge& b, unsigned max_steps)
        : user_propagator_base(&s), solver(s), native(b), limit(max_steps) {
        register_created();
        register_eq();
        register_final();
    }
    void observe(z3::expr const& e) {
        if (!observed.insert(e.id()).second) return;
        native.pin(e);
        if (z3::eq(e.get_sort(), native.sorts.at("SqlQuery"))) terms.push_back(e);
        if (e.is_app()) {
            if (native.opcodes.count(e.decl().id())) applications.push_back(e);
            for (unsigned j = 0; j < e.num_args(); ++j) observe(e.arg(j));
        }
    }
    void created(z3::expr const& e) override { ++creations; observe(e); }
    void eq(z3::expr const&, z3::expr const&) override { ++equalities; }
    void push() override { ++depth; }
    void pop(unsigned n) override {
        depth -= n;
        // Consequences may have been discarded with their solver scope.
        emitted.clear();
    }
    z3::user_propagator_base* fresh(z3::context&) override {
        throw std::runtime_error("SQL solver requires the non-cloning simple SMT solver");
    }
    void begin_check() { emitted.clear(); incomplete = false; }
    void final() override {
        ++finals;
        if (functional_congruence() || incomplete) return;
        auto count = terms.size();
        unsigned matches = 0;
        for (size_t j = 0; j < count; ++j) {
            z3::expr t = terms[j];
            if (!t.is_app() || native.opcode(t) == 0) continue;
            if (emit(t, t)) return;
            std::vector<std::vector<z3::expr>> alternatives;
            for (unsigned k = 0; k < t.num_args(); ++k) {
                z3::expr arg = t.arg(k);
                z3::expr start = solver.congruence_root(arg);
                z3::expr alt = start;
                unsigned visits = 0;
                alternatives.emplace_back();
                do {
                    if (++visits > limit) { incomplete = true; return; }
                    alternatives.back().push_back(alt);
                    alt = solver.congruence_next(alt);
                } while (!z3::eq(alt, start));
            }
            z3::expr_vector args(ctx());
            std::function<bool(unsigned, z3::expr, bool)> match =
                [&](unsigned k, z3::expr guard, bool changed) {
                    if (k == alternatives.size()) {
                        if (++matches > limit) { incomplete = true; return false; }
                        if (!changed) return false;
                        z3::expr variant = native.pin(t.decl()(args));
                        return emit(t, variant, &guard);
                    }
                    for (auto const& alt : alternatives[k]) {
                        args.push_back(alt);
                        bool different = !z3::eq(alt, t.arg(k));
                        auto premise = different ? guard && (t.arg(k) == alt) : guard;
                        if (match(k + 1, premise, changed || different)) return true;
                        args.pop_back();
                        if (incomplete) return false;
                    }
                    return false;
                };
            if (match(0, ctx().bool_val(true), false)) return;
            if (incomplete) return;
        }
    }
};

struct engine {
    z3::context ctx;
    bridge native;
    z3::solver solver;
    propagator prop;
    explicit engine(unsigned limit = 10000)
        : native(ctx), solver(ctx, z3::solver::simple{}), prop(solver, native, limit) {
        initialize_signature(native);
        active = &native;
        solver.set("auto_config", false);
    }
    void add(std::string const& input) {
        auto assertions = native.parse(input);
        for (auto const& a : assertions) { prop.observe(a); solver.add(a); }
    }
    z3::check_result check() {
        active = &native;
        prop.begin_check();
        auto r = solver.check();
        return r == z3::sat && prop.incomplete ? z3::unknown : r;
    }
};

static void self_test() {
    struct test { char const* input; z3::check_result expected; };
    test cases[] = {
        {"(assert (distinct (sql.filter sql.true (sql.scan \"t\")) (sql.scan \"t\")))", z3::unsat},
        {"(assert (distinct (sql.countOne (sql.scan \"t\")) (sql.count (sql.scan \"t\"))))", z3::unsat},
        {"(assert (distinct (sql.scan (str.++ \"ord\" \"ers\")) (sql.scan \"orders\")))", z3::unsat},
        {"(assert (distinct (sql.scan \"a\") (sql.scan \"b\")))", z3::sat},
        {"(declare-const x SqlQuery)(assert (= x (sql.filter (sql.predicate 0) (sql.scan \"t\"))))"
         "(assert (distinct (sql.filter (sql.predicate 0) x) x))", z3::unsat},
    };
    for (auto const& t : cases) {
        engine e;
        e.add(t.input);
        if (e.check() != t.expected) throw std::runtime_error("self-test result mismatch");
    }
    engine e;
    auto assertions = e.native.parse(
          "(declare-const x SqlQuery)(declare-const p SqlPred)"
          "(declare-const a SqlQuery)(declare-const b SqlQuery)"
          "(assert (= x (sql.unionAll a b)))"
          "(assert (distinct (sql.filter p x) (sql.unionAll (sql.filter p a) (sql.filter p b))))"
          "(assert (distinct x (sql.unionAll a b)))");
    for (auto const& a : assertions) e.prop.observe(a);
    e.solver.push();
    e.solver.add(assertions[0]);
    e.solver.add(assertions[1]);
    if (e.check() != z3::unsat || e.prop.egraph_rewrites == 0)
        throw std::runtime_error("e-graph matching did not establish the guarded rewrite");
    e.solver.pop();
    e.solver.add(assertions[2]);
    e.solver.add(assertions[1]);
    if (e.check() != z3::sat) throw std::runtime_error("a branch-local match leaked across pop");
    std::cout << "SQL Cherry self-tests passed\n";
}
} // namespace sql

extern "C" uint32_t Sql_Native_opcode(Z3_ast t) {
    return sql::active->opcode(z3::expr(sql::active->ctx, t));
}
extern "C" Z3_ast Sql_Native_child(Z3_ast t, uint32_t index) {
    return sql::active->pin(z3::expr(sql::active->ctx, t).arg(index));
}
extern "C" uint64_t Sql_Native_identifier(Z3_ast t) {
    return sql::active->pin(z3::expr(sql::active->ctx, t)).id();
}
extern "C" Z3_ast Sql_Native_lookup(uint64_t id) { return sql::active->pinned.at(id); }
extern "C" Z3_ast Sql_Native_make0(uint32_t op) { return sql::active->make(op, {}); }
extern "C" Z3_ast Sql_Native_make1(uint32_t op, Z3_ast a) { return sql::active->make(op, {a}); }
extern "C" Z3_ast Sql_Native_make2(uint32_t op, Z3_ast a, Z3_ast b) {
    return sql::active->make(op, {a, b});
}
extern "C" Z3_ast Sql_Native_make3(uint32_t op, Z3_ast a, Z3_ast b, Z3_ast c) {
    return sql::active->make(op, {a, b, c});
}

int main(int argc, char** argv) {
    try {
        unsigned limit = 10000, timeout = 0;
        bool stats = false;
        std::string file;
        for (int j = 1; j < argc; ++j) {
            std::string arg = argv[j];
            if (arg == "--self-test") { sql::self_test(); return 0; }
            if (arg == "--signature") { std::cout << sql::signature_text; return 0; }
            if (arg == "--stats") stats = true;
            else if ((arg == "--max-steps" || arg == "--timeout") && j + 1 < argc) {
                auto n = std::stoul(argv[++j]);
                if (n > UINT32_MAX) throw std::runtime_error("numeric option is out of range");
                if (arg == "--max-steps") limit = static_cast<unsigned>(n);
                else timeout = static_cast<unsigned>(n);
            }
            else if (!file.empty()) throw std::runtime_error("expected one SMT-LIB input file");
            else file = arg;
        }
        sql::engine e(limit);
        if (timeout) e.solver.set("timeout", timeout);
        std::stringstream input;
        if (file.empty() || file == "-") input << std::cin.rdbuf();
        else {
            std::ifstream stream(file);
            if (!stream) throw std::runtime_error("cannot open input: " + file);
            input << stream.rdbuf();
        }
        e.add(input.str());
        auto result = e.check();
        std::cout << result << "\n";
        if (result == z3::unknown)
            std::cerr << (e.prop.incomplete ? "SQL rewrite resource limit" : e.solver.reason_unknown()) << "\n";
        if (stats)
            std::cerr << "finals=" << e.prop.finals << " rewrites=" << e.prop.rewrites
                      << " egraph_rewrites=" << e.prop.egraph_rewrites
                      << " congruences=" << e.prop.congruences
                      << " created=" << e.prop.creations << " equalities=" << e.prop.equalities << "\n";
        return 0;
    }
    catch (std::exception const& error) { std::cerr << error.what() << "\n"; return 1; }
}
