#include "native.h"

#include <algorithm>
#include <charconv>
#include <chrono>
#include <exception>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <optional>
#include <sstream>
#include <utility>

namespace checker {
using Clock = std::chrono::steady_clock;

template<class T, void (*Drop)(T)>
class Owned {
public:
    T value;
    explicit Owned(T value) : value(value) {}
    ~Owned() { Drop(value); }
    Owned(Owned const&) = delete;
    Owned& operator=(Owned const&) = delete;
};

class Count {
public:
    cherry_int value = CHERRY_INT_SMALL(0);
    Count() = default;
    ~Count() { cherry_dec(value); }
    Count(Count const&) = delete;
    Count& operator=(Count const&) = delete;
    void add(cherry_int n) {
        auto next = cherry_int_add(value, n);
        cherry_dec(value);
        value = next;
    }
};

struct Options {
    bool statistics = false;
    bool diagnostics = false;
    bool sorted_core = false;
    bool clause_proofs = false;
    bool interactive = false;
    uint32_t timeout = 0;
    std::string path;
};

static std::string sort_shape(Z3AstTheory_sort sort, unsigned depth) {
    if (cherry_tag(sort) == Z3ASTTHEORY_BASESORT) {
        auto name = text(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(sort)->name);
        return name == "Bool" || name == "Int" || name == "Real" ? name : "U";
    }
    if (!depth)
        return "Array";
    auto* array = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(sort);
    std::string result = "Array[";
    bool first = true;
    each<Prims_list__sort_Cons_s>(array->domain, [&](auto domain) {
        if (!std::exchange(first, false))
            result += ",";
        result += sort_shape(domain, depth - 1);
    });
    return result + ";" + sort_shape(array->range, depth - 1) + "]";
}

static Z3AstTheory_sort expression_sort(Z3AstTheory_expr expression) {
    switch (cherry_tag(expression)) {
    case Z3ASTTHEORY_VAR: return reinterpret_cast<Z3AstTheory_expr_Var_s*>(expression)->s;
    case Z3ASTTHEORY_APP: return reinterpret_cast<Z3AstTheory_expr_App_s*>(expression)->decl.range;
    case Z3ASTTHEORY_QUANTIFIER: return reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(expression)->qsort;
    default: throw NativeError("Invalid extracted expression tag");
    }
}

static std::string escaped(std::string const& value) {
    std::ostringstream out;
    for (unsigned char c : value) {
        switch (c) {
        case '\\': out << "\\\\"; break;
        case '"': out << "\\\""; break;
        case '\n': out << "\\n"; break;
        case '\r': out << "\\r"; break;
        case '\t': out << "\\t"; break;
        case '\b': out << "\\b"; break;
        default:
            if (c >= 32 && c < 127)
                out << c;
            else
                out << '\\' << std::setw(3) << std::setfill('0') << unsigned(c);
        }
    }
    return out.str();
}

class Fingerprint {
    unsigned budget = 96;
    std::map<std::string, std::string> aliases;
public:
    std::string expression(Z3AstTheory_expr value, unsigned depth = 5) {
        if (!depth || !budget)
            return "_" + sort_shape(expression_sort(value), 2);
        --budget;
        switch (cherry_tag(value)) {
        case Z3ASTTHEORY_VAR: {
            auto* variable = reinterpret_cast<Z3AstTheory_expr_Var_s*>(value);
            return "var" + integer(variable->idx) + ":" + sort_shape(variable->s, 2);
        }
        case Z3ASTTHEORY_QUANTIFIER: {
            auto* quantified = reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(value);
            std::string kind = quantified->qk == Z3ASTTHEORY_FORALL_K ? "forall" :
                quantified->qk == Z3ASTTHEORY_EXISTS_K ? "exists" : "lambda";
            return kind + "(" + expression(quantified->body, depth - 1) + ")";
        }
        case Z3ASTTHEORY_APP: {
            auto* app = reinterpret_cast<Z3AstTheory_expr_App_s*>(value);
            auto const& decl = app->decl;
            std::string head;
            if (decl.interp.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT &&
                cherry_int_eq(decl.interp.val.Some, Z3Cherry_rational_op)) {
                std::vector<cherry_int> parameters;
                each<Prims_list__int_Cons_s>(decl.int_params, [&](auto n) { parameters.push_back(n); });
                head = parameters.size() == 2 ? integer(parameters[0]) + "/" + integer(parameters[1]) :
                    "malformed-numeral";
                if (head.size() > 64)
                    head = "large-numeral";
            }
            else if (decl.interp.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT)
                head = escaped(text(decl.decl_name));
            else {
                auto key = text(decl.decl_name);
                auto found = aliases.find(key);
                if (found == aliases.end())
                    found = aliases.emplace(key, "u" + std::to_string(aliases.size())).first;
                head = found->second;
            }
            auto result = head + ":" + sort_shape(decl.range, 2);
            if (!cherry_is_scalar(app->args)) {
                result += "(";
                auto cursor = app->args;
                for (unsigned i = 0; !cherry_is_scalar(cursor); ++i) {
                    if (i)
                        result += ",";
                    if (i == 8) {
                        result += "...arity=" + std::to_string(length<Prims_list__expr_Cons_s>(cursor));
                        break;
                    }
                    auto* cell = reinterpret_cast<Prims_list__expr_Cons_s*>(cursor);
                    result += expression(cell->hd, depth - 1);
                    cursor = cell->tl;
                }
                result += ")";
            }
            return result;
        }
        default: throw NativeError("Invalid extracted expression tag");
        }
    }
    std::string judgment(Z3UnifiedProof_judgment const& value) {
        switch (value.tag) {
        case Z3UNIFIEDPROOF_HOLDS: return "holds(" + expression(value.val.Holds) + ")";
        case Z3UNIFIEDPROOF_EQUAL: {
            auto left = expression(value.val.Equal.left);
            return "eq(" + left + " -> " + expression(value.val.Equal.right) + ")";
        }
        case Z3UNIFIEDPROOF_OBSERVATIONAL: {
            auto left = expression(value.val.Observational.left);
            return "oeq(" + left + " -> " + expression(value.val.Observational.right) + ")";
        }
        default: throw NativeError("Invalid extracted judgment tag");
        }
    }
};

static std::string rule_name(Z3UnifiedProof_rule const& rule) {
    switch (rule.tag) {
#define RULE(tag, name) case Z3UNIFIEDPROOF_##tag: return name
    RULE(ASSERTED, "asserted"); RULE(DEFAXIOM, "def-axiom");
    RULE(DEFINITIONINTRODUCTION, "intro-def"); RULE(APPLYDEFINITION, "apply-def");
    RULE(HYPOTHESIS, "hypothesis"); RULE(LEMMARULE, "lemma");
    RULE(ARITHMETICFARKAS, "arith/farkas"); RULE(ARITHMETICGOMORY, "arith/lp-gomory");
    RULE(FINITEFIELDPAC, "th-lemma");
    RULE(REWRITERULE, "rewrite"); RULE(PULLQUANTIFIER, "pull-quant");
    RULE(DESTRUCTIVEEQUALITYRESOLUTION, "der"); RULE(SKOLEMIZATION, "sk");
    RULE(ELIMUNUSED, "elim-unused"); RULE(PUSHQUANTIFIER, "push-quant");
    RULE(DESTRUCTIVEEQUALITY, "der"); RULE(REFLEXIVITY, "refl"); RULE(SYMMETRY, "symm");
    RULE(TRANSITIVITY, "trans"); RULE(TRANSITIVITYPATH, "trans*");
    RULE(CONGRUENCE, "monotonicity"); RULE(COMMUTATIVITY, "commutativity");
    RULE(MODUSPONENS, "mp"); RULE(OBSERVATIONALMP, "mp~"); RULE(IFFOBSERVATIONAL, "iff~");
    RULE(UNITRESOLUTION, "unit-resolution"); RULE(ANDELIMINATION, "and-elim");
    RULE(NOTORELIMINATION, "not-or-elim"); RULE(IFFTRUE, "iff-true"); RULE(IFFFALSE, "iff-false");
    RULE(QUANTIFIERINSTANTIATION, "quant-inst");
#undef RULE
    case Z3UNIFIEDPROOF_UNVERIFIED: return text(rule.val.Unverified);
    case Z3UNIFIEDPROOF_QUANTIFIERINTRODUCTION: {
        auto const& certificate = rule.val.QuantifierIntroduction;
        auto root = certificate.binder_root;
        if (cherry_int_lt(root, CHERRY_INT_SMALL(0)) ||
            cherry_int_ge(root, cherry_int_of_u64(length<Prims_list__binder_entry_Cons_s>(
                certificate.binder_entries))))
            return "binder";
        uint64_t index = 0, wanted = cherry_int_to_u64(root);
        std::string result;
        each<Prims_list__binder_entry_Cons_s>(certificate.binder_entries, [&](auto const& entry) {
            if (index++ == wanted)
                result = text(entry.binder_name);
        });
        return result;
    }
    default: throw NativeError("Invalid extracted proof-rule tag");
    }
}

static char const* stage_name(Z3ProofDocument_diagnostic_stage stage) {
    switch (stage) {
#define STAGE(tag, name) case Z3PROOFDOCUMENT_##tag: return name
    STAGE(LOGICALDECLARATIONS, "logical-declarations");
    STAGE(EXPRESSIONWELLFORMEDNESS, "expression-well-formedness");
    STAGE(ORIGINALASSERTIONS, "original-assertions"); STAGE(ASSERTIONSCOPE, "assertion-scope");
    STAGE(DEFINITIONCOLLECTION, "definition-collection"); STAGE(DEFINITIONCYCLE, "definition-cycle");
    STAGE(DEFINITIONEXPANSION, "definition-expansion"); STAGE(SKOLEMCOLLECTION, "skolem-collection");
    STAGE(SKOLEMCYCLE, "skolem-cycle"); STAGE(SKOLEMFRESHNESS, "skolem-freshness");
    STAGE(INPUTCLASSIFICATION, "input-classification"); STAGE(PROOFENTRY, "proof-entry");
    STAGE(MISSINGPREMISE, "missing-premise"); STAGE(MISSINGROOT, "missing-root");
    STAGE(OPENROOT, "open-root"); STAGE(DEFINITIONFRESHNESS, "definition-freshness");
#undef STAGE
    default: throw NativeError("Invalid extracted diagnostic-stage tag");
    }
}

static void report_diagnostics(Z3ProofDocument_document_diagnostic const& value, Result result) {
    if (value.tag == Z3PROOFDOCUMENT_DOCUMENTCHECKED &&
        result.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT &&
        cherry_int_eq(value.val.DocumentChecked.pending, result.val.Some)) {
        struct Group { Count count; std::string first; };
        using Key = std::pair<std::string, std::string>;
        std::map<Key, Group> groups;
        Count total;
        each<Prims_list__unmet_obligation_Cons_s>(value.val.DocumentChecked.obligations,
            [&](auto const& obligation) {
                Key key{rule_name(obligation.obligation_rule),
                    Fingerprint().judgment(obligation.obligation_conclusion)};
                auto [found, inserted] = groups.try_emplace(std::move(key));
                if (inserted)
                    found->second.first = integer(obligation.obligation_index);
                found->second.count.add(obligation.obligation_count);
                total.add(obligation.obligation_count);
            });
        if (!cherry_int_eq(total.value, result.val.Some))
            throw NativeError("Diagnostic obligation count mismatch");
        std::cerr << "diagnostic\tchecked\tpending=" << integer(result.val.Some)
                  << "\tfamilies=" << groups.size() << '\n';
        std::vector<decltype(groups)::const_iterator> order;
        for (auto it = groups.begin(); it != groups.end(); ++it)
            order.push_back(it);
        std::sort(order.begin(), order.end(), [](auto a, auto b) {
            auto comparison = cherry_int_cmp(a->second.count.value, b->second.count.value);
            return comparison ? comparison > 0 : a->first < b->first;
        });
        for (auto it : order)
            std::cerr << "obligation\t" << it->first.first << '\t'
                      << integer(it->second.count.value) << '\t' << it->second.first
                      << '\t' << it->first.second << '\n';
    }
    else if (value.tag == Z3PROOFDOCUMENT_DOCUMENTREJECTED &&
             result.tag == FSTAR_PERVASIVES_NATIVE_NONE__INT) {
        auto const& rejected = value.val.DocumentRejected;
        std::cerr << "diagnostic\trejected\tstage=" << stage_name(rejected.stage)
                  << "\tindex=" << (rejected.index.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT ?
                      integer(rejected.index.val.Some) : "-");
        if (rejected.source.tag == FSTAR_PERVASIVES_NATIVE_SOME__EXPR)
            std::cerr << "\tholds(" << Fingerprint().expression(rejected.source.val.Some) << ")";
        std::cerr << '\n';
    }
    else
        throw NativeError("Diagnostic result disagrees with document checker");
}

struct Report {
    int status;
    std::string verdict;
    std::string statistics;
};

static double milliseconds(Clock::time_point end, Clock::time_point start) {
    return std::chrono::duration<double, std::milli>(end - start).count();
}

static Report check_proof(z3::context& context, Options const& options, Clock::time_point start,
                          Clock::time_point solved, std::vector<Z3_ast> const& assertions, Z3_ast proof) {
    NativeSession session(context);
    Owned<Prims_list__ast, checker_drop_asts> roots(list<Prims_list__ast_Cons_s>(assertions));
    Owned<Z3Cherry_marshaled, checker_drop_marshaled> marshaled(Z3Cherry_marshal(roots.value, proof));
    auto const& doc = marshaled.value.document;
    auto marshal_end = Clock::now();
    bool datatype = !cherry_is_scalar(marshaled.value.schema.cases);
    bool sorted = datatype || options.sorted_core;
    // Without --diagnostics the document is checked once by Z3Cherry_check. With --diagnostics it is
    // checked once by Z3Cherry_diagnose and the verdict is read from that result: F* proves
    // diagnostic_result (diagnose ...) == check ... (Z3ProofDocument.lemma_diagnose_document_using and
    // Z3SortedProof.lemma_diagnose_document), the fact on which the OCaml driver takes its verdict from
    // check_document_diagnosed*. A second checking pass would only repeat the work.
    std::optional<Owned<Result, checker_drop_result>> checked;
    std::optional<Owned<Z3ProofDocument_document_diagnostic, checker_drop_diagnostic>> diagnosed;
    Result result{};
    if (options.diagnostics) {
        diagnosed.emplace(Z3Cherry_diagnose(sorted, marshaled.value));
        auto const& value = diagnosed->value;
        if (value.tag == Z3PROOFDOCUMENT_DOCUMENTCHECKED) {
            result.tag = FSTAR_PERVASIVES_NATIVE_SOME__INT;
            result.val.Some = value.val.DocumentChecked.pending;
        }
        else
            result.tag = FSTAR_PERVASIVES_NATIVE_NONE__INT;
    }
    else {
        checked.emplace(Z3Cherry_check(sorted, marshaled.value));
        result = checked->value;
    }
    auto check_end = Clock::now();
    std::ostringstream summary;
    summary << std::fixed << std::setprecision(3)
            << "solve_ms=" << milliseconds(solved, start)
            << " marshal_ms=" << milliseconds(marshal_end, solved)
            << " check_ms=" << milliseconds(check_end, marshal_end)
            << " expressions=" << length<Prims_list__expr_Cons_s>(doc.expressions)
            << " declarations=" << length<Prims_list__func_decl_Cons_s>(doc.declarations)
            << " proof_nodes=" << length<Prims_list__entry_Cons_s>(doc.entries)
            << " semantics=" << (datatype ? "sorted-datatype" : sorted ? "sorted-core" : "legacy");
    if (options.statistics)
        std::cerr << summary.str() << '\n';
    if (options.diagnostics) {
        report_diagnostics(diagnosed->value, result);
        if (options.statistics)
            std::cerr << std::fixed << std::setprecision(3)
                      << "diagnose_ms=" << milliseconds(Clock::now(), check_end) << '\n';
    }
    size_t edges = 0, binder_nodes = 0, binder_edges = 0;
    each<Prims_list__entry_Cons_s>(doc.entries, [&](auto const& entry) {
        edges += length<Prims_list__int_Cons_s>(entry.premise_ids);
        if (entry.rule.tag == Z3UNIFIEDPROOF_QUANTIFIERINTRODUCTION)
            each<Prims_list__binder_entry_Cons_s>(
                entry.rule.val.QuantifierIntroduction.binder_entries, [&](auto const& bound) {
                    ++binder_nodes;
                    binder_edges += length<Prims_list__int_Cons_s>(bound.binder_premises);
                });
    });
    bool rejected = result.tag == FSTAR_PERVASIVES_NATIVE_NONE__INT;
    auto pending = rejected ? "unknown" : integer(result.val.Some);
    summary << " assertions=" << assertions.size() << " proof_edges=" << edges
            << " binder_nodes=" << binder_nodes << " binder_edges=" << binder_edges
            << " pending=" << pending;
    int status = rejected ? 1 : pending == "0" ? 0 : 3;
    return {status, rejected ? "REJECT" : pending == "0" ? "ACCEPT" : "PARTIAL " + pending, summary.str()};
}

static bool whitespace(char c) { return c == ' ' || c == '\t' || c == '\r' || c == '\n'; }

static bool read_command(std::istream& input, std::string& result) {
    result.clear();
    bool comment = false;
    char c;
    while (input.get(c)) {
        if (comment) {
            if (c == '\n')
                comment = false;
        }
        else if (c == ';')
            comment = true;
        else if (!whitespace(c)) {
            if (c != '(')
                throw NativeError("expected an SMT-LIB command beginning with '('");
            result += c;
            break;
        }
    }
    if (result.empty()) {
        if (input.bad())
            throw NativeError("Cannot read SMT-LIB input");
        return false;
    }
    enum Mode { Normal, Comment, Quoted, String, AfterQuote };
    Mode mode = Normal;
    size_t depth = 1;
    while (input.get(c)) {
        if (!c)
            throw NativeError("null character in SMT-LIB input");
        result += c;
        if (mode == AfterQuote) {
            if (c == '"') {
                mode = String;
                continue;
            }
            mode = Normal;
        }
        switch (mode) {
        case Comment: if (c == '\n') mode = Normal; break;
        case Quoted: if (c == '|') mode = Normal; break;
        case String: if (c == '"') mode = AfterQuote; break;
        case Normal:
            switch (c) {
            case ';': mode = Comment; break;
            case '|': mode = Quoted; break;
            case '"': mode = String; break;
            case '(': ++depth; break;
            case ')': if (!--depth) return true; break;
            default: break;
            }
            break;
        case AfterQuote: break;
        }
    }
    throw NativeError("incomplete SMT-LIB command at end of input");
}

static std::string command_name(std::string const& command) {
    size_t i = 1;
    bool comment = false;
    while (i < command.size()) {
        char c = command[i];
        if (comment) {
            if (c == '\n')
                comment = false;
        }
        else if (c == ';')
            comment = true;
        else if (!whitespace(c))
            break;
        ++i;
    }
    bool quoted = i < command.size() && command[i] == '|';
    if (quoted)
        ++i;
    size_t first = i;
    while (i < command.size() && (quoted ? command[i] != '|' :
           !whitespace(command[i]) && command[i] != ')' && command[i] != '(' && command[i] != ';'))
        ++i;
    return command.substr(first, i - first);
}

struct Interactive {
    z3::context& context;
    Options const& options;
    Clock::time_point start;
    bool rejected = false;
    bool partial = false;
    std::string report;
    std::exception_ptr callback_error;

    static Z3_string callback(void* user, Z3_context, Z3_ast proof, Z3_ast_vector inputs) noexcept {
        auto& self = *static_cast<Interactive*>(user);
        try {
            auto solved = Clock::now();
            std::vector<Z3_ast> assertions;
            for (unsigned i = 0, n = Z3_ast_vector_size(self.context, inputs); i < n; ++i)
                assertions.push_back(Z3_ast_vector_get(self.context, inputs, i));
            auto report = check_proof(self.context, self.options, self.start, solved, assertions, proof);
            self.rejected |= report.status == 1;
            self.partial |= report.status == 3;
            self.report = "; proof-check " + report.verdict + "\n; proof-stats " + report.statistics;
            return self.report.c_str();
        }
        catch (...) {
            // Never unwind through Z3's callback; the caller rethrows after evaluation.
            self.callback_error = std::current_exception();
            return nullptr;
        }
    }
};

static std::string evaluate(z3::context& context, std::string const& command) {
    auto output = Z3_eval_smtlib2_string(context, command.c_str());
    context.check_error();
    if (!output)
        throw NativeError("SMT-LIB evaluation returned no response");
    return output;
}

static int interactive(z3::context& context, Options const& options) {
    Interactive state{context, options, Clock::now(), false, false, {}, {}};
    struct Registration {
        z3::context& context;
        ~Registration() { Z3_set_proof_check_callback(context, nullptr, nullptr); }
    } registration{context};
    Z3_set_proof_check_callback(context, &state, Interactive::callback);
    context.check_error();
    auto initialize = [&] {
        evaluate(context, "(set-option :produce-proofs true)(set-option :timeout " +
            std::to_string(options.timeout) + ")" +
            (options.clause_proofs ? "(set-option :smt.clause_proof true)" : ""));
    };
    initialize();
    bool error = false;
    auto report_error = [&](std::string const& message) {
        error = true;
        std::cout << "(error \"";
        for (char c : message) {
            if (c == '"')
                std::cout << '"';
            std::cout << c;
        }
        std::cout << "\")\n" << std::flush;
    };
    std::string command;
    while (read_command(std::cin, command)) {
        auto name = command_name(command);
        try {
            state.start = Clock::now();
            auto output = evaluate(context, command);
            if (state.callback_error)
                std::rethrow_exception(state.callback_error);
            if (name == "reset")
                initialize();
            if (name == "set-option") {
                auto production = evaluate(context, "(get-option :produce-proofs)");
                production.erase(std::remove_if(production.begin(), production.end(), whitespace), production.end());
                if (production == "false") {
                    evaluate(context, "(set-option :produce-proofs true)");
                    throw NativeError("interactive mode requires :produce-proofs true");
                }
            }
            std::cout << output << std::flush;
            if (name == "exit")
                break;
        }
        catch (z3::exception const& exception) {
            if (state.callback_error)
                std::rethrow_exception(state.callback_error);
            report_error(exception.msg());
        }
        catch (NativeError const& exception) {
            if (state.callback_error)
                std::rethrow_exception(state.callback_error);
            report_error(exception.what());
        }
    }
    return error ? 2 : state.rejected ? 1 : state.partial ? 3 : 0;
}

static char const* usage =
    "usage: checker [--interactive] [--clause-proofs] [--stats] [--diagnostics] "
    "[--sorted-core] [--timeout-ms N] [input.smt2]\n"
    "  --interactive    Evaluate stdin commands and certify each UNSAT proof\n"
    "  --clause-proofs  Certify clausal SMT search proofs\n"
    "  --stats          Report phase timings and marshaled node counts\n"
    "  --diagnostics    Report typed unmet-obligation fingerprints\n"
    "  --sorted-core    Use sort-indexed checking without legacy fallback\n"
    "  --version        Report the embedded Z3 version\n"
    "  --timeout-ms N   Solver timeout, 0..4294967295 milliseconds (0 is unlimited)\n";

static int run(int argc, char** argv) {
    if (argc == 2 && std::string(argv[1]) == "--version") {
        unsigned major, minor, build, revision;
        Z3_get_version(&major, &minor, &build, &revision);
        std::cout << major << '.' << minor << '.' << build << '.' << revision << '\n';
        return 0;
    }
    Options options;
    bool anonymous = false, has_path = false;
    for (int i = 1; i < argc; ++i) {
        std::string argument = argv[i];
        if (!anonymous && (argument == "--help" || argument == "-help" || argument == "-h")) {
            std::cout << usage;
            return 0;
        }
        if (!anonymous && argument == "--")
            anonymous = true;
        else if (!anonymous && argument == "--interactive") options.interactive = true;
        else if (!anonymous && argument == "--stats") options.statistics = true;
        else if (!anonymous && argument == "--diagnostics") options.diagnostics = true;
        else if (!anonymous && argument == "--sorted-core") options.sorted_core = true;
        else if (!anonymous && argument == "--clause-proofs") options.clause_proofs = true;
        else if (!anonymous && (argument == "--timeout-ms" || argument.starts_with("--timeout-ms="))) {
            std::string value;
            if (argument == "--timeout-ms") {
                if (++i == argc)
                    throw NativeError("missing --timeout-ms value");
                value = argv[i];
            }
            else
                value = argument.substr(argument.find('=') + 1);
            auto [end, error] = std::from_chars(value.data(), value.data() + value.size(), options.timeout);
            if (error != std::errc() || end != value.data() + value.size())
                throw NativeError("invalid --timeout-ms");
        }
        else {
            if (!anonymous && argument != "-" && argument.starts_with("-"))
                throw NativeError("unknown option: " + argument);
            if (has_path)
                throw NativeError("expected at most one SMT-LIB input file");
            options.path = argument;
            has_path = true;
        }
    }
    if (options.interactive && has_path && options.path != "-")
        throw NativeError("--interactive reads commands from stdin, not an input file");
    z3::config config;
    config.set("proof", true);
    config.set("timeout", std::to_string(options.timeout).c_str());
    z3::context context(config);
    custard_init_globals();
    if (options.interactive)
        return interactive(context, options);
    std::ifstream file;
    std::istream* input = &std::cin;
    if (has_path && options.path != "-") {
        file.open(options.path, std::ios::binary);
        if (!file)
            throw NativeError("cannot open input file: " + options.path);
        input = &file;
    }
    std::ostringstream contents;
    contents << input->rdbuf();
    if (input->bad())
        throw NativeError("cannot read SMT-LIB input");
    auto source = contents.str();
    if (source.find('\0') != std::string::npos)
        throw NativeError("null character in SMT-LIB input");
    auto start = Clock::now();
    auto assertions = context.parse_string(source.c_str());
    z3::solver solver(context);
    if (options.clause_proofs) {
        z3::params parameters(context);
        parameters.set("clause_proof", true);
        solver.set(parameters);
    }
    solver.add(assertions);
    auto result = solver.check();
    if (result == z3::sat) {
        std::cout << "SAT\n";
        return 4;
    }
    if (result == z3::unknown) {
        std::cout << "UNKNOWN " << solver.reason_unknown() << '\n';
        return 5;
    }
    auto solved = Clock::now();
    auto proof = solver.proof();
    std::vector<Z3_ast> roots;
    for (unsigned i = 0; i < assertions.size(); ++i)
        roots.push_back(assertions[i]);
    auto report = check_proof(context, options, start, solved, roots, proof);
    std::cout << report.verdict << '\n';
    return report.status;
}
}

int main(int argc, char** argv) {
    try {
        return checker::run(argc, argv);
    }
    catch (checker::NativeError const& exception) {
        std::cerr << "ERROR " << exception.what() << '\n';
    }
    catch (z3::exception const& exception) {
        std::cerr << "ERROR " << exception.msg() << '\n';
    }
    catch (std::bad_alloc const&) {
        std::cerr << "ERROR native checker ran out of memory\n";
    }
    return 2;
}
