#include "native.h"
#include "readable.h"

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
    bool readable = false;
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

// Precedence-aware infix text of an obligation conclusion, for the `expression` machine rows that follow each `obligation`
// row. It mirrors Z3NativeMain.pretty_judgment in the OCaml checker with the same bounds: 512 visited nodes and depth 12 per
// judgment, at most 32 arguments or binders, 64-character numerals and 256-byte names. A numeral is compared with 10^64
// before it is converted, so no input yields an unbounded string. Nothing here feeds back into checking.
class Pretty {
    // F* Z3ValueTheory tags. The extracted checker exports only the rational tag (Z3Cherry_rational_op);
    // tools/test_native_checker.py compares these with the F* source.
    static constexpr int64_t op_not = 1;
    static constexpr int64_t op_plus = 2;
    static constexpr int64_t op_eq = 7;
    static constexpr int64_t op_and = 13;
    static constexpr int64_t op_or = 14;
    static constexpr int64_t op_mul = 17;
    static constexpr int64_t op_arith_add = 23;
    static constexpr int64_t op_arith_mul = 24;
    static constexpr int64_t op_arith_sub = 25;
    static constexpr int64_t op_arith_div = 26;
    static constexpr int64_t op_arith_le = 27;
    static constexpr int64_t op_arith_lt = 28;
    static constexpr int64_t op_arith_ge = 29;
    static constexpr int64_t op_arith_gt = 30;
    unsigned budget = 512, next_bound = 0;

    // "decl!ID:NAME" and "sort!ID:NAME" (native ids) are shown as NAME.
    static std::string original_name(std::string const& prefix, std::string const& name) {
        auto marker = prefix + "!";
        if (name.compare(0, marker.size(), marker) != 0)
            return name;
        auto stop = name.find(':', marker.size());
        if (stop == std::string::npos || stop == marker.size())
            return name;
        for (auto i = marker.size(); i < stop; ++i)
            if (name[i] < '0' || name[i] > '9')
                return name;
        return name.substr(stop + 1);
    }
    static std::string symbol(std::string const& name) {
        auto safe = [](unsigned char c) {
            return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
                c == '_' || c == '.' || c == '$' || c == '!';
        };
        if (!name.empty() && name.size() <= 256 && std::all_of(name.begin(), name.end(), safe) &&
            !(name[0] >= '0' && name[0] <= '9') && name != "and" && name != "or" && name != "not" &&
            name != "forall" && name != "exists" && name != "lambda")
            return name;
        return "|" + escaped(name.size() > 256 ? name.substr(0, 256) + "..." : name) + "|";
    }
    // At most limit + 1 cells are visited.
    template<class Cell>
    static size_t length_up_to(cherry_obj* values, size_t limit) {
        size_t result = 0;
        while (!cherry_is_scalar(values) && result <= limit) {
            ++result;
            values = reinterpret_cast<Cell*>(values)->tl;
        }
        return result;
    }
    std::string sort(Z3AstTheory_sort value, unsigned depth) {
        if (cherry_tag(value) == Z3ASTTHEORY_BASESORT)
            return symbol(original_name("sort", text(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(value)->name)));
        auto* array = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(value);
        if (!depth || length_up_to<Prims_list__sort_Cons_s>(array->domain, 32) > 32)
            return "Array";
        std::string result = "Array[";
        bool first = true;
        each<Prims_list__sort_Cons_s>(array->domain, [&](auto domain) {
            if (!std::exchange(first, false))
                result += ", ";
            result += sort(domain, depth - 1);
        });
        return result + "; " + sort(array->range, depth - 1) + "]";
    }
    // A rational numeral n/d with d > 0 shows n, or n/d when d is not 1; text longer than 64 characters is elided.
    static std::optional<std::string> numeral_text(cherry_int n, cherry_int d) {
        struct Bounds {
            cherry_int upper = cherry_int_of_decimal(("1" + std::string(64, '0')).c_str());
            cherry_int lower = cherry_int_neg(upper);
            ~Bounds() {
                cherry_dec(upper);
                cherry_dec(lower);
            }
        };
        static Bounds const bounds;
        // |n| >= 10^64 or d >= 10^64 already has more than 64 characters.
        if (!cherry_int_lt(n, bounds.upper) || !cherry_int_gt(n, bounds.lower) || !cherry_int_lt(d, bounds.upper))
            return std::nullopt;
        auto result = integer(n) + (cherry_int_eq(d, CHERRY_INT_SMALL(1)) ? "" : "/" + integer(d));
        if (result.size() > 64)
            return std::nullopt;
        return result;
    }
    std::string expression(Z3AstTheory_expr value, unsigned depth, std::vector<std::string> const& environment,
                           int minimum) {
        if (!depth || !budget)
            return "...:" + sort(expression_sort(value), 2);
        --budget;
        auto render = [&](int least, Z3AstTheory_expr argument) {
            return expression(argument, depth - 1, environment, least);
        };
        int precedence = 100;
        std::string result;
        switch (cherry_tag(value)) {
        case Z3ASTTHEORY_VAR: {
            auto index = reinterpret_cast<Z3AstTheory_expr_Var_s*>(value)->idx;
            if (cherry_int_ge(index, CHERRY_INT_SMALL(0)) &&
                cherry_int_lt(index, cherry_int_of_u64(environment.size())))
                result = environment[cherry_int_to_u64(index)];
            else
                result = "#" + readable::integer_text(index);
            break;
        }
        case Z3ASTTHEORY_QUANTIFIER: {
            auto* quantified = reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(value);
            if (length_up_to<Prims_list__sort_Cons_s>(quantified->bound_sorts, 32) > 32) {
                result = "...:" + sort(expression_sort(value), 2);
                break;
            }
            std::vector<std::string> names, declarations;
            each<Prims_list__sort_Cons_s>(quantified->bound_sorts, [&](auto) {
                names.push_back("#b" + std::to_string(next_bound++));
            });
            size_t i = 0;
            each<Prims_list__sort_Cons_s>(quantified->bound_sorts, [&](auto bound) {
                declarations.push_back(names[i++] + ":" + sort(bound, 3));
            });
            std::vector<std::string> inner(names.rbegin(), names.rend());
            inner.insert(inner.end(), environment.begin(), environment.end());
            precedence = 0;
            result = std::string(quantified->qk == Z3ASTTHEORY_FORALL_K ? "forall" :
                quantified->qk == Z3ASTTHEORY_EXISTS_K ? "exists" : "lambda") + " (";
            for (size_t k = 0; k < declarations.size(); ++k)
                result += (k ? ", " : "") + declarations[k];
            result += "). " + expression(quantified->body, depth - 1, inner, 0);
            break;
        }
        case Z3ASTTHEORY_APP: {
            auto* app = reinterpret_cast<Z3AstTheory_expr_App_s*>(value);
            auto const& decl = app->decl;
            bool interpreted = decl.interp.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT;
            auto is = [&](int64_t tag) { return interpreted && cherry_int_eq(decl.interp.val.Some, CHERRY_INT_SMALL(tag)); };
            auto name = interpreted ? text(decl.decl_name) : original_name("decl", text(decl.decl_name));
            auto count = length_up_to<Prims_list__expr_Cons_s>(app->args, 32);
            std::vector<Z3AstTheory_expr> arguments;
            if (count <= 32)
                each<Prims_list__expr_Cons_s>(app->args, [&](auto argument) { arguments.push_back(argument); });
            auto infix = [&](int level, char const* token, bool strict) {
                precedence = level;
                for (size_t k = 0; k < arguments.size(); ++k)
                    result += (k ? std::string(" ") + token + " " : std::string()) +
                        render(strict || k > 0 ? level + 1 : level, arguments[k]);
            };
            if (count > 32)
                result = "...:" + sort(decl.range, 2);
            else if (interpreted && cherry_int_eq(decl.interp.val.Some, Z3Cherry_rational_op) && arguments.empty()) {
                std::vector<cherry_int> parameters;
                if (length_up_to<Prims_list__int_Cons_s>(decl.int_params, 2) == 2)
                    each<Prims_list__int_Cons_s>(decl.int_params, [&](auto n) { parameters.push_back(n); });
                if (parameters.size() == 2 && cherry_int_gt(parameters[1], CHERRY_INT_SMALL(0))) {
                    auto numeral = numeral_text(parameters[0], parameters[1]);
                    if (!numeral)
                        result = "...:" + sort(decl.range, 2);
                    else {
                        result = *numeral;
                        precedence = !cherry_int_eq(parameters[1], CHERRY_INT_SMALL(1)) ? 50 :
                            cherry_int_lt(parameters[0], CHERRY_INT_SMALL(0)) ? 60 : 100;
                    }
                }
                else
                    result = symbol(name);
            }
            else if (is(op_not) && arguments.size() == 1) {
                precedence = 60;
                result = "not " + render(61, arguments[0]);
            }
            else if (is(op_arith_sub) && arguments.size() == 1) {
                precedence = 60;
                result = "-" + render(61, arguments[0]);
            }
            else if (arguments.size() >= 2 && is(op_or)) infix(10, "or", false);
            else if (arguments.size() >= 2 && is(op_and)) infix(20, "and", false);
            else if (arguments.size() == 2 && is(op_eq)) infix(30, "=", true);
            else if (arguments.size() == 2 && is(op_arith_le)) infix(30, "<=", true);
            else if (arguments.size() == 2 && is(op_arith_lt)) infix(30, "<", true);
            else if (arguments.size() == 2 && is(op_arith_ge)) infix(30, ">=", true);
            else if (arguments.size() == 2 && is(op_arith_gt)) infix(30, ">", true);
            else if (arguments.size() >= 2 && (is(op_arith_add) || is(op_plus))) infix(40, "+", false);
            else if (arguments.size() >= 2 && is(op_arith_sub)) infix(40, "-", false);
            else if (arguments.size() >= 2 && (is(op_arith_mul) || is(op_mul))) infix(50, "*", false);
            else if (arguments.size() == 2 && is(op_arith_div)) infix(50, "/", false);
            else {
                result = symbol(name);
                if (!arguments.empty()) {
                    result += "(";
                    for (size_t k = 0; k < arguments.size(); ++k)
                        result += (k ? ", " : "") + render(0, arguments[k]);
                    result += ")";
                }
            }
            break;
        }
        default: throw NativeError("Invalid extracted expression tag");
        }
        return precedence < minimum ? "(" + result + ")" : result;
    }
public:
    std::string judgment(Z3UnifiedProof_judgment const& value) {
        switch (value.tag) {
        case Z3UNIFIEDPROOF_HOLDS: return expression(value.val.Holds, 12, {}, 0);
        case Z3UNIFIEDPROOF_EQUAL: {
            auto left = expression(value.val.Equal.left, 12, {}, 31);
            return left + " = " + expression(value.val.Equal.right, 12, {}, 31);
        }
        case Z3UNIFIEDPROOF_OBSERVATIONAL: {
            auto left = expression(value.val.Observational.left, 12, {}, 31);
            return left + " ~ " + expression(value.val.Observational.right, 12, {}, 31);
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
        // The first obligation of a family names its node and, as in the OCaml driver, gives the conclusion of its expression row.
        struct Group { Count count; std::string first; Z3UnifiedProof_judgment conclusion{}; };
        using Key = std::pair<std::string, std::string>;
        std::map<Key, Group> groups;
        Count total;
        each<Prims_list__unmet_obligation_Cons_s>(value.val.DocumentChecked.obligations,
            [&](auto const& obligation) {
                Key key{rule_name(obligation.obligation_rule),
                    Fingerprint().judgment(obligation.obligation_conclusion)};
                auto [found, inserted] = groups.try_emplace(std::move(key));
                if (inserted) {
                    found->second.first = integer(obligation.obligation_index);
                    found->second.conclusion = obligation.obligation_conclusion;
                }
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
        for (auto it : order) {
            std::cerr << "obligation\t" << it->first.first << '\t'
                      << integer(it->second.count.value) << '\t' << it->second.first
                      << '\t' << it->first.second << '\n';
            std::cerr << "expression\t" << it->first.first << '\t'
                      << integer(it->second.count.value) << '\t' << it->second.first
                      << '\t' << Pretty().judgment(it->second.conclusion) << '\n';
        }
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

// One block per query: the representative of each of the first max_families obligation families, in
// the order of the machine rows. The node index is the position of the obligation in the document's
// proof entries, which is where its premise ids are read from. Mirrors Z3NativeMain.Readable.report_text.
static std::string readable_report(unsigned query, std::string const& verdict,
                                   Z3ProofDocument_document_Mk_document_s const& doc,
                                   Z3ProofDocument_document_diagnostic const& diagnostic) {
    using namespace readable;
    std::string out;
    bool full = false;
    auto emit = [&](std::string const& block) {
        if (full)
            return;
        if (out.size() + block.size() > max_report_chars)
            full = true;
        else
            out += block;
    };
    auto entry_at = [&](cherry_int index) -> Z3ProofDocument_entry const* {
        if (!cherry_is_scalar(index) || cherry_int_lt(index, CHERRY_INT_SMALL(0)))
            return nullptr;
        uint64_t wanted = cherry_int_to_u64(index), position = 0;
        for (auto cursor = doc.entries; !cherry_is_scalar(cursor);) {
            auto* cell = reinterpret_cast<Prims_list__entry_Cons_s*>(cursor);
            if (position++ == wanted)
                return &cell->hd;
            cursor = cell->tl;
        }
        return nullptr;
    };
    auto premise_list = [](std::vector<cherry_int> const& ids) {
        if (ids.empty())
            return std::string("none");
        std::string result;
        for (size_t i = 0; i < ids.size() && i < max_premises; ++i)
            result += (i ? " #" : "#") + integer_text(ids[i]);
        if (ids.size() > max_premises)
            result += " ...<" + std::to_string(ids.size() - max_premises) + " more>";
        return result;
    };
    auto family_block = [&](size_t position, size_t total, std::string const& rule, cherry_int count,
                            size_t members, Z3ProofDocument_unmet_obligation const& first) {
        auto const index = first.obligation_index;
        std::string block = "readable\tfamily=" + std::to_string(position) + "/" + std::to_string(total) +
            "\trule=" + rule + "\tcount=" + integer_text(count) + "\tmembers=" + std::to_string(members) +
            "\tnode=" + integer_text(index) + "\tnode-pending=" + integer_text(first.obligation_count) + "\n";
        std::vector<Z3UnifiedProof_judgment const*> premises;
        each<Prims_list__judgment_Cons_s>(first.obligation_premises,
            [&](auto const& premise) { premises.push_back(&premise); });
        std::vector<cherry_int> ids;
        auto const* entry = entry_at(index);
        std::string unmapped;
        if (!entry)
            unmapped = "no document entry at this index";
        else if (rule_name(entry->rule) != rule)
            unmapped = "the document entry at this index has another rule or premise count";
        else {
            each<Prims_list__int_Cons_s>(entry->premise_ids, [&](auto id) { ids.push_back(id); });
            if (ids.size() != premises.size())
                unmapped = "the document entry at this index has another rule or premise count";
        }
        bool const known = unmapped.empty();
        block += "  node " + integer_text(index) + ": " +
            (known ? "premises: " + premise_list(ids) :
                "no source-node mapping (" + unmapped + "): premise ids unavailable") + "\n";
        for (size_t k = 0; k < premises.size() && k < max_premises; ++k)
            block += "  premise " + (known ? "#" + integer_text(ids[k]) : "[" + std::to_string(k) + "]") +
                ": " + judgment_text(*premises[k]).first + "\n";
        if (premises.size() > max_premises)
            block += "  ...<" + std::to_string(premises.size() - max_premises) + " more premises omitted>\n";
        auto conclusion = judgment_text(first.obligation_conclusion);
        block += "  conclusion: " + conclusion.first + "\n";
        Z3UnifiedProof_judgment holds{};
        holds.tag = Z3UNIFIEDPROOF_HOLDS;
        holds.val.Holds = first.obligation_source;
        auto source = judgment_text(holds);
        block += source.first == conclusion.first && !conclusion.second && !source.second ?
            std::string("  source formula: same as conclusion\n") :
            "  source formula: " + source.first + "\n";
        return block;
    };
    if (diagnostic.tag == Z3PROOFDOCUMENT_DOCUMENTCHECKED) {
        struct Family {
            Count count;
            size_t members = 0;
            Z3ProofDocument_unmet_obligation const* first = nullptr;
        };
        using Key = std::pair<std::string, std::string>;
        std::map<Key, Family> families;
        each<Prims_list__unmet_obligation_Cons_s>(diagnostic.val.DocumentChecked.obligations,
            [&](auto const& obligation) {
                auto [found, inserted] = families.try_emplace(
                    Key{rule_name(obligation.obligation_rule),
                        Fingerprint().judgment(obligation.obligation_conclusion)});
                if (inserted)
                    found->second.first = &obligation;
                found->second.count.add(obligation.obligation_count);
                ++found->second.members;
            });
        std::vector<std::map<Key, Family>::const_iterator> order;
        for (auto it = families.begin(); it != families.end(); ++it)
            order.push_back(it);
        std::sort(order.begin(), order.end(), [](auto a, auto b) {
            auto comparison = cherry_int_cmp(a->second.count.value, b->second.count.value);
            return comparison ? comparison > 0 : a->first < b->first;
        });
        size_t total = order.size(), shown = std::min<size_t>(total, max_families);
        emit("readable\tquery=" + std::to_string(query) + "\tverdict=" + verdict + "\tpending=" +
             integer_text(diagnostic.val.DocumentChecked.pending) + "\tfamilies=" + std::to_string(total) +
             "\tshown=" + std::to_string(shown) + "\n");
        for (size_t i = 0; i < shown; ++i)
            emit(family_block(i + 1, total, order[i]->first.first, order[i]->second.count.value,
                              order[i]->second.members, *order[i]->second.first));
        if (total > shown)
            emit("readable\tomitted\tfamilies=" + std::to_string(total - shown) + "\treason=family-limit\n");
        if (full)
            out += "readable\tomitted\treason=report-size\n";
    }
    else {
        auto const& rejected = diagnostic.val.DocumentRejected;
        bool has_index = rejected.index.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT;
        std::string block = "readable\tquery=" + std::to_string(query) + "\tverdict=" + verdict +
            "\tstage=" + stage_name(rejected.stage) + "\tindex=" +
            (has_index ? integer_text(rejected.index.val.Some) : std::string("-")) + "\n";
        if (has_index && (rejected.stage == Z3PROOFDOCUMENT_PROOFENTRY ||
                          rejected.stage == Z3PROOFDOCUMENT_MISSINGPREMISE)) {
            auto const index = rejected.index.val.Some;
            if (auto const* entry = entry_at(index)) {
                std::vector<cherry_int> ids;
                each<Prims_list__int_Cons_s>(entry->premise_ids, [&](auto id) { ids.push_back(id); });
                block += "  node " + integer_text(index) + ": rule=" + rule_name(entry->rule) +
                    " premises: " + premise_list(ids) + "\n";
            }
            else
                block += "  node " + integer_text(index) +
                    ": no source-node mapping (no document entry at this index)\n";
        }
        if (rejected.source.tag == FSTAR_PERVASIVES_NATIVE_SOME__EXPR) {
            Z3UnifiedProof_judgment holds{};
            holds.tag = Z3UNIFIEDPROOF_HOLDS;
            holds.val.Holds = rejected.source.val.Some;
            block += "  source formula: " + judgment_text(holds).first + "\n";
        }
        else
            block += "  source formula: none reported\n";
        emit(block);
    }
    out += "readable\tend\tquery=" + std::to_string(query) + "\n";
    return out;
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
                          Clock::time_point solved, std::vector<Z3_ast> const& assertions, Z3_ast proof,
                          unsigned query) {
    NativeSession session(context);
    Owned<Prims_list__ast, checker_drop_asts> roots(list<Prims_list__ast_Cons_s>(assertions));
    Owned<Z3Cherry_marshaled, checker_drop_marshaled> marshaled(Z3Cherry_marshal(roots.value, proof));
    // document is [@@cherry_boxed]: a counted cell holding the record.
    auto const& doc = *reinterpret_cast<Z3ProofDocument_document_Mk_document_s const*>(marshaled.value.document);
    auto marshal_end = Clock::now();
    bool datatype = !cherry_is_scalar(marshaled.value.schema.cases);
    bool sorted = datatype || options.sorted_core;
    // Without --diagnostics the document is checked once by Z3Cherry_check. With --diagnostics it is
    // checked once by Z3Cherry_diagnose and the verdict is read from that result: F* proves
    // diagnostic_result (diagnose ...) == check ... (Z3ProofDocument.lemma_diagnose_document_using and
    // Z3SortedProof.lemma_diagnose_document_epsilon), the fact on which the OCaml driver takes its verdict from
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
        if (options.readable) {
            std::string verdict = result.tag == FSTAR_PERVASIVES_NATIVE_NONE__INT ? "REJECT" :
                cherry_int_eq(result.val.Some, CHERRY_INT_SMALL(0)) ? "ACCEPT" :
                "PARTIAL " + integer(result.val.Some);
            std::cerr << readable_report(query, verdict, doc, diagnosed->value) << std::flush;
        }
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
    unsigned queries = 0;

    static Z3_string callback(void* user, Z3_context, Z3_ast proof, Z3_ast_vector inputs) noexcept {
        auto& self = *static_cast<Interactive*>(user);
        try {
            auto solved = Clock::now();
            std::vector<Z3_ast> assertions;
            for (unsigned i = 0, n = Z3_ast_vector_size(self.context, inputs); i < n; ++i)
                assertions.push_back(Z3_ast_vector_get(self.context, inputs, i));
            auto report = check_proof(self.context, self.options, self.start, solved, assertions, proof,
                                      ++self.queries);
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
    Interactive state{context, options, Clock::now(), false, false, {}, {}, 0};
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
    "usage: checker [--interactive] [--clause-proofs] [--stats] [--diagnostics] [--readable] "
    "[--sorted-core] [--timeout-ms N] [input.smt2]\n"
    "  --interactive    Evaluate stdin commands and certify each UNSAT proof\n"
    "  --clause-proofs  Certify clausal SMT search proofs\n"
    "  --stats          Report phase timings and marshaled node counts\n"
    "  --diagnostics    Report typed unmet-obligation fingerprints\n"
    "  --readable       Also print bounded readable pending/rejected conditions (implies --diagnostics)\n"
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
        else if (!anonymous && argument == "--readable") options.readable = options.diagnostics = true;
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
    auto report = check_proof(context, options, start, solved, roots, proof, 1);
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
