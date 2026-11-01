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
#include <string>
#include <utility>
#include <vector>

// readable_report is a static function of the checker's driver. The driver is compiled into this test, with its main renamed away and
// never called, so the report branches that no command line reaches are tested on the real function (not on a copy).
#define main checker_driver_main
#include "main.cpp"
#undef main

namespace {
using namespace checker;

// --readable renders what the checker saw, within explicit bounds. The expressions are built by hand,
// as in the OCaml bridge tests (readable_conditions), so malformed metadata and shapes no solver
// produces are covered next to the ordinary ones.
cherry_int z(int64_t n) { return cherry_int_of_i64(n); }
cherry_string str(std::string const& value) { return cherry_str_of_bytes(value.data(), value.size()); }

Z3AstTheory_sort base(std::string const& name) {
    auto* cell = reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(
        cherry_alloc(sizeof(Z3AstTheory_sort_BaseSort_s), Z3ASTTHEORY_BASESORT));
    cell->name = str(name);
    return &cell->hdr;
}

Z3AstTheory_sort array(std::vector<Z3AstTheory_sort> const& domain, Z3AstTheory_sort range) {
    auto* cell = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(
        cherry_alloc(sizeof(Z3AstTheory_sort_ArraySort_s), Z3ASTTHEORY_ARRAYSORT));
    cell->domain = list<Prims_list__sort_Cons_s>(domain);
    cell->range = range;
    return &cell->hdr;
}

Z3AstTheory_func_decl declaration(std::string const& name, std::vector<Z3AstTheory_sort> const& domain,
                                  Z3AstTheory_sort range, std::optional<cherry_int> interp = std::nullopt,
                                  std::vector<cherry_int> const& parameters = {}) {
    FStar_Pervasives_Native_option__int tag{};
    if (interp)
        tag = some<FStar_Pervasives_Native_option__int>(*interp);
    return {str(name), list<Prims_list__sort_Cons_s>(domain), range, tag,
            list<Prims_list__int_Cons_s>(parameters)};
}

Z3AstTheory_expr app(Z3AstTheory_func_decl const& decl, std::vector<Z3AstTheory_expr> const& arguments = {}) {
    auto* cell = reinterpret_cast<Z3AstTheory_expr_App_s*>(
        cherry_alloc(sizeof(Z3AstTheory_expr_App_s), Z3ASTTHEORY_APP));
    cell->decl = decl;
    cell->args = list<Prims_list__expr_Cons_s>(arguments);
    return &cell->hdr;
}

Z3AstTheory_expr constant(std::string const& name, Z3AstTheory_sort range,
                          std::optional<cherry_int> interp = std::nullopt,
                          std::vector<cherry_int> const& parameters = {}) {
    return app(declaration(name, {}, range, interp, parameters));
}

Z3AstTheory_expr variable(int64_t index, Z3AstTheory_sort sort) {
    auto* cell = reinterpret_cast<Z3AstTheory_expr_Var_s*>(
        cherry_alloc(sizeof(Z3AstTheory_expr_Var_s), Z3ASTTHEORY_VAR));
    cell->idx = z(index);
    cell->s = sort;
    return &cell->hdr;
}

Z3AstTheory_expr quantifier(Z3AstTheory_quantifier_kind kind, std::vector<Z3AstTheory_sort> const& sorts,
                            Z3AstTheory_sort sort, Z3AstTheory_expr body) {
    auto* cell = reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(
        cherry_alloc(sizeof(Z3AstTheory_expr_Quantifier_s), Z3ASTTHEORY_QUANTIFIER));
    cell->qk = kind;
    cell->bound_sorts = list<Prims_list__sort_Cons_s>(sorts);
    cell->qsort = sort;
    cell->body = body;
    return &cell->hdr;
}

readable::Rendered text(Z3AstTheory_expr value) {
    Z3UnifiedProof_judgment holds{};
    holds.tag = Z3UNIFIEDPROOF_HOLDS;
    holds.val.Holds = value;
    return readable::judgment_text(holds);
}

bool contains(std::string const& whole, std::string const& part) {
    return whole.find(part) != std::string::npos;
}

bool readable_regressions() {
    bool ok = true;
    auto expect = [&](char const* label, readable::Rendered const& actual, std::string const& expected) {
        if (actual.first != expected) {
            std::cerr << "readable " << label << ": " << actual.first << ", expected " << expected << '\n';
            ok = false;
        }
    };
    auto require = [&](char const* label, bool condition) {
        if (!condition) {
            std::cerr << "readable " << label << '\n';
            ok = false;
        }
    };
    auto int_sort = base("Int"), bool_sort = base("Bool"), real_sort = base("Real"), bv8 = base("BV8"),
         bv32 = base("BV32");
    auto decimal = [](std::string const& digits) { return cherry_int_of_decimal(digits.c_str()); };
    auto numeral = [&](cherry_int n, cherry_int d, Z3AstTheory_sort range) {
        return constant("numeral", range, Z3Cherry_rational_op, {n, d});
    };
    // F* Z3BvLemma.op_numeral / op_extract, Z3ValueTheory.op_and / op_not
    auto bv_numeral_tag = CHERRY_INT_SMALL(108), extract_tag = CHERRY_INT_SMALL(111),
         and_tag = CHERRY_INT_SMALL(13), not_tag = CHERRY_INT_SMALL(1);
    // values and sorts
    expect("integer numeral", text(numeral(z(5), z(1), int_sort)), "holds(5)");
    expect("rational numeral", text(numeral(z(-7), z(3), real_sort)), "holds(-7/3:Real)");
    expect("integral real numeral", text(numeral(z(2), z(1), real_sort)), "holds(2:Real)");
    expect("bit-vector numeral", text(constant("bv", base("BV8"), bv_numeral_tag, {z(8), z(255)})),
           "holds((_ bv255 8))");
    expect("wide bit-vector numeral",
           text(constant("bv", base("BV64"), bv_numeral_tag, {z(64), decimal("18446744073709551615")})),
           "holds((_ bv18446744073709551615 64))");
    expect("extraction parameters",
           text(app(declaration("extract", {bv32}, bv8, extract_tag, {z(32), z(15), z(8)}), {variable(0, bv32)})),
           "holds((extract[32,15,8]:BV8 #0:BV32))");
    expect("multi-index array", text(variable(0, array({int_sort, int_sort}, bool_sort))),
           "holds(#0:(Array Int Int Bool))");
    expect("nested array", text(variable(1, array({int_sort}, array({bv8}, bool_sort)))),
           "holds(#1:(Array Int (Array BV8 Bool)))");
    auto inner = quantifier(Z3ASTTHEORY_EXISTS_K, {bv8}, bool_sort, variable(1, int_sort));
    expect("nested binders",
           text(quantifier(Z3ASTTHEORY_FORALL_K, {int_sort, array({int_sort}, bool_sort)}, bool_sort, inner)),
           "holds((forall [Int (Array Int Bool)] (exists [BV8] #1:Int)))");
    expect("lambda",
           text(quantifier(Z3ASTTHEORY_LAMBDA_K, {int_sort}, array({int_sort}, bool_sort), variable(0, int_sort))),
           "holds((lambda [Int] #0:Int))");
    // identity: same-named declarations stay apart, datatype operations are not connectives
    auto x = constant("decl!3:x", int_sort), y = constant("decl!4:y", real_sort);
    expect("first same-named function", text(app(declaration("decl!7:f", {int_sort}, int_sort), {x})),
           "holds((f#7:Int x#3:Int))");
    expect("second same-named function", text(app(declaration("decl!9:f", {real_sort}, int_sort), {y})),
           "holds((f#9:Int y#4:Real))");
    expect("uninterpreted symbol without a native id", text(constant("g", bool_sort)), "holds(g#-:Bool)");
    expect("user sort", text(constant("decl!6:t", base("sort!5:T"))), "holds(t#6:T#5)");
    auto p = constant("decl!1:p", bool_sort), q = constant("decl!2:q", bool_sort);
    expect("Boolean connective",
           text(app(declaration("and", {bool_sort, bool_sort}, bool_sort, and_tag), {p, q})),
           "holds((and p#1:Bool q#2:Bool))");
    auto owner = base("sort!5:T");
    expect("accessor named like a connective",
           text(app(declaration("and", {owner}, bool_sort, Z3Cherry_accessor_op, {z(5), z(12), z(0)}),
                    {constant("decl!6:t", owner)})),
           "holds((and@accessor[5,12,0]:Bool t#6:T#5))");
    expect("constructor named like a constant",
           text(constant("true", owner, Z3Cherry_constructor_op, {z(5), z(13), z(0)})),
           "holds(true@constructor[5,13,0]:T#5)");
    // names
    expect("Unicode name", text(constant("decl!3:h\xc3\xa9llo \xe2\x98\x83", int_sort)),
           "holds(|h\xc3\xa9llo \xe2\x98\x83|#3:Int)");
    expect("bar, backslash and control bytes", text(constant("decl!4:a|b\\c\n", int_sort)),
           "holds(|a\\x7cb\\x5cc\\x0a|#4:Int)");
    expect("invalid UTF-8", text(constant("decl!5:\xff\xc0\x80\xed\xa0\x80", int_sort)),
           "holds(|\\xff\\xc0\\x80\\xed\\xa0\\x80|#5:Int)");
    expect("C1 control", text(constant("decl!5:\xc2\x85", int_sort)), "holds(|\\xc2\\x85|#5:Int)");
    expect("empty name", text(constant("", int_sort)), "holds(||#-:Int)");
    expect("name starting with a digit", text(constant("1x", int_sort)), "holds(|1x|#-:Int)");
    expect("long name", text(constant("decl!1:" + std::string(300, 'a'), int_sort)),
           "holds(|" + std::string(96, 'a') + "...<204 more bytes>|#1:Int)");
    // numerals are checked against 10^100 before they are converted
    std::string nines(100, '9');
    expect("100-digit numeral", text(numeral(decimal(nines), z(1), int_sort)), "holds(" + nines + ")");
    expect("negative 100-digit numeral", text(numeral(decimal("-" + nines), z(1), int_sort)),
           "holds(-" + nines + ")");
    expect("101-digit numeral", text(numeral(decimal("1" + std::string(100, '0')), z(1), int_sort)),
           "holds(<+huge integer: more than 100 digits omitted>)");
    expect("negative huge numeral", text(numeral(decimal("-1" + std::string(400, '0')), z(1), int_sort)),
           "holds(<-huge integer: more than 100 digits omitted>)");
    expect("5000-digit numerator", text(numeral(decimal("1" + std::string(5000, '0')), z(3), int_sort)),
           "holds(<+huge integer: more than 100 digits omitted>/3)");
    // malformed metadata is shown as reflected, never repaired
    expect("rational without a denominator", text(constant("5", int_sort, Z3Cherry_rational_op, {z(5)})),
           "holds(|5|[5]:Int)");
    expect("bit-vector numeral without a value", text(constant("bv", bv8, bv_numeral_tag, {z(8)})),
           "holds(bv[8]:BV8)");
    expect("bit-vector numeral with an extra parameter",
           text(constant("bv", bv8, bv_numeral_tag, {z(8), z(255), z(1)})), "holds(bv[8,255,1]:BV8)");
    expect("unknown interpretation", text(constant("weird", bool_sort, CHERRY_INT_SMALL(999))), "holds(weird)");
    std::vector<cherry_int> forty;
    for (int i = 0; i < 40; ++i)
        forty.push_back(z(i));
    std::string sixteen;
    for (int i = 0; i < 16; ++i)
        sixteen += (i ? "," : "") + std::to_string(i);
    expect("parameter limit", text(constant("decl!1:p", bool_sort, std::nullopt, forty)),
           "holds(p#1[" + sixteen + ",<24 more>]:Bool)");
    // limits leave explicit markers and stay cheap
    auto started = std::chrono::steady_clock::now();
    auto negation = declaration("not", {bool_sort}, bool_sort, not_tag);
    auto deep = p;
    for (int i = 0; i < 200000; ++i)
        deep = app(negation, {deep});
    auto rendered = text(deep);
    require("deep expression was not cut",
            rendered.second && contains(rendered.first, "<...depth>") && rendered.first.size() < 400);
    auto pair = declaration("decl!8:g", {int_sort, int_sort}, int_sort);
    auto dag = x;
    for (int i = 0; i < 100; ++i)
        dag = app(pair, {dag, dag});
    rendered = text(dag);
    require("shared DAG output was not bounded",
            rendered.second && rendered.first.size() <= readable::max_chars + 16);
    std::vector<Z3AstTheory_expr> fives(5000, numeral(z(5), z(1), int_sort));
    rendered = text(app(declaration("decl!8:h", {}, int_sort), fives));
    require("node limit left no marker", rendered.second && contains(rendered.first, "<...nodes>"));
    rendered = text(variable(0, array(std::vector<Z3AstTheory_sort>(3000, int_sort), bool_sort)));
    require("character limit left no marker",
            rendered.second && contains(rendered.first, "<...chars>") &&
            rendered.first.size() <= readable::max_chars + 16);
    auto nested = bool_sort;
    for (int i = 0; i < 100; ++i)
        nested = array({int_sort}, nested);
    rendered = text(variable(0, nested));
    require("sort depth limit left no marker", rendered.second && contains(rendered.first, "<...depth>"));
    require("rendering was not cheap",
            std::chrono::steady_clock::now() - started < std::chrono::seconds(30));
    return ok;
}

Z3UnifiedProof_rule unverified(std::string const& name) {
    Z3UnifiedProof_rule rule{};
    rule.tag = Z3UNIFIEDPROOF_UNVERIFIED;
    rule.val.Unverified = str(name);
    return rule;
}

Z3UnifiedProof_judgment holds_of(Z3AstTheory_expr value) {
    Z3UnifiedProof_judgment judgment{};
    judgment.tag = Z3UNIFIEDPROOF_HOLDS;
    judgment.val.Holds = value;
    return judgment;
}

Z3UnifiedProof_judgment equal_of(Z3AstTheory_expr left, Z3AstTheory_expr right) {
    Z3UnifiedProof_judgment judgment{};
    judgment.tag = Z3UNIFIEDPROOF_EQUAL;
    judgment.val.Equal.left = left;
    judgment.val.Equal.right = right;
    return judgment;
}

Z3ProofDocument_entry entry_of(std::string const& rule, Z3AstTheory_expr formula, std::vector<cherry_int> const& premise_ids) {
    return {unverified(rule), formula, list<Prims_list__int_Cons_s>(premise_ids)};
}

Z3ProofDocument_document_Mk_document_s document_of(std::vector<Z3ProofDocument_entry> const& entries) {
    Z3ProofDocument_document_Mk_document_s value{};
    value.declarations = value.expressions = value.assertions = CHERRY_SCALAR(0);
    value.entries = list<Prims_list__entry_Cons_s>(entries);
    value.root = z(0);
    return value;
}

Z3ProofDocument_unmet_obligation obligation_of(std::string const& rule, int64_t index, cherry_int count,
                                               Z3UnifiedProof_judgment conclusion,
                                               std::vector<Z3UnifiedProof_judgment> const& premises,
                                               Z3AstTheory_expr source) {
    return {z(index), unverified(rule), conclusion, list<Prims_list__judgment_Cons_s>(premises), source, count};
}

Z3ProofDocument_document_diagnostic checked_of(cherry_int pending, std::vector<Z3ProofDocument_unmet_obligation> const& obligations) {
    Z3ProofDocument_document_diagnostic value{};
    value.tag = Z3PROOFDOCUMENT_DOCUMENTCHECKED;
    value.val.DocumentChecked.pending = pending;
    value.val.DocumentChecked.obligations = list<Prims_list__unmet_obligation_Cons_s>(obligations);
    return value;
}

Z3ProofDocument_document_diagnostic rejected_of(Z3ProofDocument_diagnostic_stage stage, std::optional<int64_t> index,
                                                std::optional<Z3AstTheory_expr> source) {
    Z3ProofDocument_document_diagnostic value{};
    value.tag = Z3PROOFDOCUMENT_DOCUMENTREJECTED;
    value.val.DocumentRejected.stage = stage;
    if (index)
        value.val.DocumentRejected.index = some<FStar_Pervasives_Native_option__int>(z(*index));
    if (source)
        value.val.DocumentRejected.source = some<FStar_Pervasives_Native_option__expr>(*source);
    return value;
}

// The `expression` machine rows (Pretty in main.cpp): the OCaml bridge test pretty_expressions expects the same strings for the same
// hand-built shapes, and report_diagnostics prints one row after each obligation row with the conclusion of the family's first
// obligation, as the OCaml driver does.
bool pretty_regressions() {
    bool ok = true;
    auto expect = [&](std::string const& label, std::string const& actual, std::string const& expected) {
        if (actual != expected) {
            std::cerr << "pretty " << label << ": " << actual << ", expected " << expected << '\n';
            ok = false;
        }
    };
    auto bool_s = base("Bool"), int_s = base("Int"), real_s = base("Real");
    auto decimal = [](std::string const& digits) { return cherry_int_of_decimal(digits.c_str()); };
    // F* Z3ValueTheory.op_not / op_eq / op_and / op_or / op_arith_add / op_arith_mul / op_arith_sub / op_arith_gt
    auto not_tag = CHERRY_INT_SMALL(1), eq_tag = CHERRY_INT_SMALL(7), and_tag = CHERRY_INT_SMALL(13),
         or_tag = CHERRY_INT_SMALL(14), add_tag = CHERRY_INT_SMALL(23), mul_tag = CHERRY_INT_SMALL(24),
         sub_tag = CHERRY_INT_SMALL(25), gt_tag = CHERRY_INT_SMALL(30);
    auto numeral = [&](cherry_int n, cherry_int d, Z3AstTheory_sort range) {
        return constant("numeral", range, Z3Cherry_rational_op, {n, d});
    };
    auto shown = [](Z3AstTheory_expr value) { return Pretty().judgment(holds_of(value)); };
    auto x = constant("decl!3:x", int_s), p = constant("decl!1:p", bool_s), q = constant("decl!2:q", bool_s),
         y = constant("decl!5:y", int_s), z_ = constant("decl!6:z", int_s), r = constant("decl!7:r", bool_s);
    auto binary = [&](cherry_int tag, std::string const& token, Z3AstTheory_expr a, Z3AstTheory_expr b) {
        return app(declaration(token, {int_s, int_s}, cherry_int_eq(tag, eq_tag) ? bool_s : int_s, tag), {a, b});
    };
    auto boolean = [&](cherry_int tag, std::string const& token, Z3AstTheory_expr a, Z3AstTheory_expr b) {
        return app(declaration(token, {bool_s, bool_s}, bool_s, tag), {a, b});
    };
    auto negation = [&](Z3AstTheory_expr a) { return app(declaration("not", {bool_s}, bool_s, not_tag), {a}); };
    auto minus = [&](Z3AstTheory_expr a) { return app(declaration("-", {int_s}, int_s, sub_tag), {a}); };
    // the OCaml bridge cases parsed from SMT-LIB, rebuilt by hand
    expect("and over or", shown(boolean(and_tag, "and", p, boolean(or_tag, "or", q, r))), "p and (q or r)");
    expect("or over and", shown(boolean(or_tag, "or", boolean(and_tag, "and", p, q), r)), "p and q or r");
    expect("nested equality", shown(boolean(eq_tag, "=", p, boolean(eq_tag, "=", q, r))), "p = (q = r)");
    expect("sum of product", shown(binary(add_tag, "+", x, binary(mul_tag, "*", y, z_))), "x + y * z");
    expect("product of sum", shown(binary(mul_tag, "*", binary(add_tag, "+", x, y), z_)), "(x + y) * z");
    expect("right-nested difference", shown(binary(sub_tag, "-", x, binary(sub_tag, "-", y, z_))), "x - (y - z)");
    expect("double negation", shown(minus(minus(x))), "-(-x)");
    expect("negated comparison", shown(negation(app(declaration("<=", {int_s, int_s}, bool_s, CHERRY_INT_SMALL(27)),
        {binary(add_tag, "+", x, binary(mul_tag, "*", y, z_)), numeral(z(0), z(1), int_s)}))), "not (x + y * z <= 0)");
    expect("uninterpreted connective", shown(constant("and", bool_s)), "|and|");
    // the shared hand-built shapes of pretty_expressions
    expect("binders", shown(quantifier(Z3ASTTHEORY_FORALL_K, {int_s, bool_s}, bool_s,
        boolean(or_tag, "or", binary(eq_tag, "=", variable(1, int_s), x), variable(0, bool_s)))),
        "forall (#b0:Int, #b1:Bool). #b0 = x or #b1");
    expect("negated binder", shown(negation(quantifier(Z3ASTTHEORY_EXISTS_K, {int_s}, bool_s,
        app(declaration(">", {int_s, int_s}, bool_s, gt_tag), {variable(0, int_s), numeral(z(0), z(1), int_s)})))),
        "not (exists (#b0:Int). #b0 > 0)");
    expect("rational summand", shown(app(declaration("+", {int_s, real_s}, real_s, add_tag),
        {x, numeral(z(-7), z(3), real_s)})), "x + -7/3");
    expect("negative factor", shown(binary(mul_tag, "*", x, numeral(z(-5), z(1), int_s))), "x * -5");
    expect("negated negative numeral", shown(minus(numeral(z(-5), z(1), int_s))), "-(-5)");
    std::string const ten63 = "1" + std::string(63, '0');
    expect("64-character numeral", shown(numeral(decimal(ten63), z(1), int_s)), ten63);
    expect("65-character numeral", shown(numeral(decimal(ten63 + "0"), z(1), int_s)), "...:Int");
    expect("65-character negative numeral", shown(numeral(decimal("-" + ten63), z(1), int_s)), "...:Int");
    expect("5000-digit numeral", shown(numeral(decimal("1" + std::string(5000, '0')), z(3), int_s)), "...:Int");
    expect("unbound variable", shown(variable(3, int_s)), "#3");
    expect("quoted name", shown(constant("decl!2:a b", int_s)), "|a b|");
    expect("long name", shown(constant("decl!9:" + std::string(300, 'a'), int_s)), "|" + std::string(256, 'a') + "...|");
    expect("uninterpreted keyword", shown(constant("decl!4:or", bool_s)), "|or|");
    expect("non-numeric id", shown(constant("decl!x:y", int_s)), "|decl!x:y|");
    auto set = array({int_s}, bool_s), owner = base("sort!5:T");
    expect("binder sorts", shown(quantifier(Z3ASTTHEORY_LAMBDA_K, {set, owner}, array({set, owner}, set), variable(1, set))),
        "lambda (#b0:Array[Int; Bool], #b1:T). #b0");
    auto f = [&](std::vector<Z3AstTheory_expr> const& arguments) {
        return app(declaration("decl!7:f", std::vector<Z3AstTheory_sort>(arguments.size(), int_s), int_s), arguments);
    };
    expect("uninterpreted application", shown(f({x, numeral(z(1), z(1), int_s)})), "f(x, 1)");
    expect("argument limit", shown(f(std::vector<Z3AstTheory_expr>(33, x))), "...:Int");
    auto deep = p;
    for (int i = 0; i < 13; ++i)
        deep = negation(deep);
    std::string nested = "not ...:Bool";
    for (int i = 0; i < 11; ++i)
        nested = "not (" + nested + ")";
    expect("depth limit", shown(deep), nested);
    expect("equality judgment", Pretty().judgment(equal_of(x, binary(add_tag, "+", x, numeral(z(1), z(1), int_s)))),
           "x = x + 1");
    Z3UnifiedProof_judgment observational{};
    observational.tag = Z3UNIFIEDPROOF_OBSERVATIONAL;
    observational.val.Observational.left = p;
    observational.val.Observational.right = boolean(or_tag, "or", p, q);
    expect("observational judgment", Pretty().judgment(observational), "p ~ (p or q)");
    // 512 visited nodes bound a shared DAG whose tree is exponential
    auto pair = declaration("decl!8:g", {int_s, int_s}, int_s);
    auto dag = x;
    for (int i = 0; i < 100; ++i)
        dag = app(pair, {dag, dag});
    auto bounded = shown(dag);
    if (bounded.size() > 20000 || bounded.find("...:Int") == std::string::npos) {
        std::cerr << "pretty node budget did not bound a shared DAG (" << bounded.size() << " characters)\n";
        ok = false;
    }
    // report_diagnostics: an expression row after each obligation row, from the first obligation of the family
    auto pending = z(5);
    auto diagnostic = checked_of(pending, {
        obligation_of("r1", 4, z(1), holds_of(boolean(or_tag, "or", p, q)), {}, p),
        obligation_of("r0", 7, z(3), equal_of(x, binary(add_tag, "+", x, numeral(z(1), z(1), int_s))), {}, x),
        obligation_of("r1", 9, z(1), holds_of(boolean(or_tag, "or", r, p)), {}, r)});
    std::ostringstream captured;
    auto* previous = std::cerr.rdbuf(captured.rdbuf());
    try {
        report_diagnostics(diagnostic, some<Result>(pending));
    }
    catch (...) {
        std::cerr.rdbuf(previous);
        throw;
    }
    std::cerr.rdbuf(previous);
    std::vector<std::string> lines;
    std::istringstream rows(captured.str());
    for (std::string line; std::getline(rows, line);)
        lines.push_back(line);
    auto prefix = [](std::string const& line, std::string const& start) { return line.rfind(start, 0) == 0; };
    bool rows_ok = lines.size() == 5 && lines[0] == "diagnostic\tchecked\tpending=5\tfamilies=2" &&
        prefix(lines[1], "obligation\tr0\t3\t7\t") && lines[2] == "expression\tr0\t3\t7\tx = x + 1" &&
        prefix(lines[3], "obligation\tr1\t2\t4\t") && lines[4] == "expression\tr1\t2\t4\tp or q";
    if (!rows_ok) {
        std::cerr << "pretty expression rows:\n" << captured.str();
        ok = false;
    }
    return ok;
}

// Cases readable_regressions does not reach, mirroring the OCaml bridge test readable_edge_cases (same expectations, written from the
// printer's contract: what the checker saw is shown as reflected and never re-encoded, repaired or reduced, an unmatched native
// identity is a plain quoted name, every limit leaves a marker) and the report goldens of its readable_conditions, run on the
// driver's own readable_report: node mapping and its absence, family and size limits, rejected documents.
bool readable_edge_cases() {
    bool ok = true;
    auto expect = [&](std::string const& label, std::string const& actual, std::string const& expected) {
        if (actual != expected) {
            std::cerr << "readable " << label << ": " << actual << ", expected " << expected << '\n';
            ok = false;
        }
    };
    auto require = [&](char const* label, bool condition) {
        if (!condition) {
            std::cerr << "readable " << label << '\n';
            ok = false;
        }
    };
    auto int_sort = base("Int"), bool_sort = base("Bool");
    auto decimal = [](std::string const& digits) { return cherry_int_of_decimal(digits.c_str()); };
    auto huge = [](char const* sign) { return std::string("<") + sign + "huge integer: more than 100 digits omitted>"; };
    auto shown = [](Z3AstTheory_expr value) { return text(value).first; };
    // F* Z3BvLemma.op_numeral / op_extract, Z3ValueTheory.op_eq (tools/test_native_checker.py guards op_numeral)
    auto bv_tag = CHERRY_INT_SMALL(108), extract_tag = CHERRY_INT_SMALL(111), eq_tag = CHERRY_INT_SMALL(7);
    auto bv_numeral = [&](int64_t width, cherry_int value) {
        return constant("bv", base("BV" + std::to_string(width)), bv_tag, {z(width), value});
    };
    // bit-vector values: encoded two's complement, negative or out of range as reflected, wide, beyond the digit limit
    expect("minimum signed value, as encoded", shown(bv_numeral(8, z(128))), "holds((_ bv128 8))");
    expect("negative value is not re-encoded", shown(bv_numeral(8, z(-1))), "holds((_ bv-1 8))");
    expect("value beyond the width is not reduced", shown(bv_numeral(8, z(256))), "holds((_ bv256 8))");
    expect("zero width", shown(bv_numeral(0, z(0))), "holds((_ bv0 0))");
    std::string const ones_256 = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    expect("256-bit all ones", shown(bv_numeral(256, decimal(ones_256))), "holds((_ bv" + ones_256 + " 256))");
    expect("value of 100 digits", shown(bv_numeral(333, decimal("1" + std::string(99, '0')))),
           "holds((_ bv1" + std::string(99, '0') + " 333))");
    expect("value of 101 digits", shown(bv_numeral(333, decimal("1" + std::string(100, '0')))),
           "holds((_ bv" + huge("+") + " 333))");
    expect("512-bit value beyond the digit limit", shown(bv_numeral(512, decimal("1" + std::string(154, '0')))),
           "holds((_ bv" + huge("+") + " 512))");
    expect("negative 512-bit value beyond the digit limit", shown(bv_numeral(512, decimal("-1" + std::string(154, '0')))),
           "holds((_ bv" + huge("-") + " 512))");
    expect("width beyond the digit limit",
           shown(constant("bv", base("BV0"), bv_tag, {decimal("1" + std::string(150, '0')), z(5)})),
           "holds((_ bv5 " + huge("+") + "))");
    // wide extractions: widths and bounds are shown as reflected, even beyond a machine word, with the range they give
    auto bv256 = base("BV256"), bv128 = base("BV128"), bv101 = base("BV101");
    auto extract = [&](std::vector<cherry_int> const& parameters, Z3AstTheory_sort domain, Z3AstTheory_sort range,
                       Z3AstTheory_expr argument) {
        return app(declaration("extract", {domain}, range, extract_tag, parameters), {argument});
    };
    expect("wide extraction", shown(extract({z(256), z(200), z(100)}, bv256, bv101, variable(0, bv256))),
           "holds((extract[256,200,100]:BV101 #0:BV256))");
    expect("extraction of a wide numeral",
           shown(extract({z(256), z(255), z(128)}, bv256, bv128, bv_numeral(256, decimal(ones_256)))),
           "holds((extract[256,255,128]:BV128 (_ bv" + ones_256 + " 256)))");
    expect("extraction bound beyond a machine word",
           shown(extract({z(256), decimal("18446744073709551621"), z(100)}, bv256, bv101, variable(0, bv256))),
           "holds((extract[256,18446744073709551621,100]:BV101 #0:BV256))");
    // declaration identities: only "decl!DIGITS:NAME" (at most 20 digits) is a native identity; any other name is kept quoted, with no id
    for (auto const& [name, expected] : std::vector<std::pair<std::string, std::string>>{
             {"decl!", "decl!#-"}, {"decl!:x", "|decl!:x|#-"}, {"decl!abc:x", "|decl!abc:x|#-"},
             {"decl!12", "decl!12#-"}, {"decl!12:", "||#12"}, {"decl!7:f:g", "|f:g|#7"},
             {"decl!7:decl!8:x", "|decl!8:x|#7"}, {"decl!007:x", "x#007"}, {"Decl!3:x", "|Decl!3:x|#-"},
             {"sort!3:x", "|sort!3:x|#-"}, {"decl!\xd9\xa3:x", "|decl!\xd9\xa3:x|#-"},
             {"decl!12345678901234567890:x", "x#12345678901234567890"},
             {"decl!123456789012345678901:x", "|decl!123456789012345678901:x|#-"}})
        expect("declaration " + name, shown(constant(name, int_sort)), "holds(" + expected + ":Int)");
    expect("interpreted head whose name looks like a native identity",
           shown(constant("decl!3:x", bool_sort, CHERRY_INT_SMALL(999))), "holds(|decl!3:x|)");
    auto p = constant("decl!1:p", bool_sort), q = constant("decl!2:q", bool_sort);
    expect("uninterpreted function named like a connective, without a native id",
           shown(app(declaration("and", {bool_sort, bool_sort}, bool_sort), {p, q})),
           "holds((and#-:Bool p#1:Bool q#2:Bool))");
    expect("uninterpreted function named like a connective, with a native id",
           shown(app(declaration("decl!5:and", {bool_sort, bool_sort}, bool_sort), {p, q})),
           "holds((and#5:Bool p#1:Bool q#2:Bool))");
    // sort identities follow the same rule with "sort!DIGITS:NAME"
    for (auto const& [name, expected] : std::vector<std::pair<std::string, std::string>>{
             {"sort!", "sort!"}, {"sort!:T", "|sort!:T|"}, {"sort!x:T", "|sort!x:T|"}, {"sort!5", "sort!5"},
             {"sort!5:", "||#5"}, {"sort!5:two words", "|two words|#5"}, {"sort!4:Int", "Int#4"},
             {"sort!8:Bool", "Bool#8"}, {"Sort!5:T", "|Sort!5:T|"}, {"decl!5:T", "|decl!5:T|"}})
        expect("sort " + name, shown(variable(0, base(name))), "holds(#0:" + expected + ")");
    expect("array sort over malformed and native sorts",
           shown(variable(0, array({base("sort!x:T"), int_sort}, base("sort!6:U")))),
           "holds(#0:(Array |sort!x:T| Int U#6))");
    // The range of an interpreted head is printed after ':' unless it is Bool (connectives and predicates: an interpreted head without a
    // range is Bool) or the sort of its first argument, which that argument prints: so the sort of an expression is always printed or
    // follows from what is printed. A constant array needs it most: its domain sorts occur nowhere in its arguments, so without the
    // range arrays over different domains read the same.
    auto real_sort = base("Real");
    // F* Z3ValueTheory op_select / op_store / op_true / op_const_array / op_ite / op_to_real / op_arith_add / op_arith_le and
    // Z3BvLemma op_add / op_concat / op_zero_extend
    auto select_tag = CHERRY_INT_SMALL(3), store_tag = CHERRY_INT_SMALL(4), true_tag = CHERRY_INT_SMALL(8),
         ite_tag = CHERRY_INT_SMALL(19), add_tag = CHERRY_INT_SMALL(23), le_tag = CHERRY_INT_SMALL(27),
         to_real_tag = CHERRY_INT_SMALL(31), const_tag = CHERRY_INT_SMALL(32), bv_add_tag = CHERRY_INT_SMALL(104),
         bv_concat_tag = CHERRY_INT_SMALL(112), zero_extend_tag = CHERRY_INT_SMALL(119), unknown_tag = CHERRY_INT_SMALL(999);
    auto zero = constant("numeral", int_sort, Z3Cherry_rational_op, {z(0), z(1)});
    auto truth = constant("true", bool_sort, true_tag);
    auto const_array = [&](std::vector<Z3AstTheory_sort> const& domains, Z3AstTheory_sort element, Z3AstTheory_expr value) {
        return app(declaration("const", {element}, array(domains, element), const_tag), {value});
    };
    auto over_int = shown(const_array({int_sort}, int_sort, zero)), over_real = shown(const_array({real_sort}, int_sort, zero));
    expect("constant array over Int", over_int, "holds((const:(Array Int Int) 0))");
    expect("constant array over Real", over_real, "holds((const:(Array Real Int) 0))");
    if (over_int == over_real) {
        std::cerr << "readable constant arrays over different domains read the same\n";
        ok = false;
    }
    expect("constant array over two domains", shown(const_array({int_sort, real_sort}, bool_sort, truth)),
           "holds((const:(Array Int Real Bool) true))");
    expect("constant array of constant arrays",
           shown(const_array({int_sort}, array({real_sort}, bool_sort), const_array({real_sort}, bool_sort, truth))),
           "holds((const:(Array Int (Array Real Bool)) (const:(Array Real Bool) true)))");
    auto arrays = array({int_sort}, int_sort);
    auto store_of = [&](Z3AstTheory_expr array_argument) {
        return app(declaration("store", {arrays, int_sort, int_sort}, arrays, store_tag), {array_argument, zero, zero});
    };
    expect("store takes the sort of its array argument", shown(store_of(variable(0, arrays))),
           "holds((store #0:(Array Int Int) 0 0))");
    expect("store of a constant array", shown(store_of(const_array({int_sort}, int_sort, zero))),
           "holds((store (const:(Array Int Int) 0) 0 0))");
    expect("select shows its element sort",
           shown(app(declaration("select", {arrays, int_sort}, int_sort, select_tag), {variable(0, arrays), zero})),
           "holds((select:Int #0:(Array Int Int) 0))");
    // operators that keep the sort of their first argument, predicates, and operators that change the sort
    auto x_real = variable(1, real_sort), y_int = variable(2, int_sort), c_bool = variable(3, bool_sort);
    auto five_real = constant("numeral", real_sort, Z3Cherry_rational_op, {z(5), z(1)});
    auto operator_of = [&](std::string const& name, cherry_int tag, std::vector<Z3AstTheory_sort> const& domain,
                           Z3AstTheory_sort range, std::vector<Z3AstTheory_expr> const& arguments,
                           std::vector<cherry_int> const& parameters = {}) {
        return app(declaration(name, domain, range, tag, parameters), arguments);
    };
    expect("sum keeps the sort of its first argument",
           shown(operator_of("+", add_tag, {real_sort, real_sort}, real_sort, {x_real, five_real})), "holds((+ #1:Real 5:Real))");
    expect("sum of integers", shown(operator_of("+", add_tag, {int_sort, int_sort}, int_sort, {zero, y_int})),
           "holds((+ 0 #2:Int))");
    expect("conversion to Real shows its range", shown(operator_of("to_real", to_real_tag, {int_sort}, real_sort, {y_int})),
           "holds((to_real:Real #2:Int))");
    expect("comparison is Bool",
           shown(operator_of("<=", le_tag, {real_sort, real_sort}, bool_sort, {x_real, five_real})), "holds((<= #1:Real 5:Real))");
    expect("conditional over integers",
           shown(operator_of("ite", ite_tag, {bool_sort, int_sort, int_sort}, int_sort, {c_bool, zero, y_int})),
           "holds((ite:Int #3:Bool 0 #2:Int))");
    expect("conditional over Bool",
           shown(operator_of("ite", ite_tag, {bool_sort, bool_sort, bool_sort}, bool_sort, {c_bool, p, q})),
           "holds((ite #3:Bool p#1:Bool q#2:Bool))");
    auto bv8 = base("BV8"), bv24 = base("BV24"), bv32 = base("BV32");
    expect("bit-vector sum keeps the sort of its first argument",
           shown(operator_of("bvadd", bv_add_tag, {bv32, bv32}, bv32, {variable(0, bv32), variable(1, bv32)}, {z(32)})),
           "holds((bvadd[32] #0:BV32 #1:BV32))");
    expect("concatenation shows its width",
           shown(operator_of("concat", bv_concat_tag, {bv24, bv8}, bv32, {variable(0, bv24), variable(1, bv8)}, {z(24), z(8)})),
           "holds((concat[24,8]:BV32 #0:BV24 #1:BV8))");
    expect("zero extension shows its width",
           shown(operator_of("zero_extend", zero_extend_tag, {bv8}, bv32, {variable(0, bv8)}, {z(8), z(24)})),
           "holds((zero_extend[8,24]:BV32 #0:BV8))");
    auto t5 = base("sort!5:T"), t6 = base("sort!6:T");
    expect("unknown interpreted head over one user sort",
           shown(operator_of("weird", unknown_tag, {t5}, t5, {constant("decl!6:t", t5)})), "holds((weird t#6:T#5))");
    expect("unknown interpreted head between two user sorts of one name",
           shown(operator_of("weird", unknown_tag, {t6}, t5, {constant("decl!6:t", t6)})), "holds((weird:T#5 t#6:T#6))");
    expect("unknown interpreted constant", shown(constant("weird", int_sort, unknown_tag)), "holds(weird:Int)");
    expect("unknown interpreted array constant", shown(constant("weird", arrays, unknown_tag)), "holds(weird:(Array Int Int))");
    expect("a user sort named Bool is not Bool", shown(constant("weird", base("sort!8:Bool"), unknown_tag)), "holds(weird:Bool#8)");
    // where the argument is cut by the depth limit the sort is printed; so are sorts too deep or too wide to be compared
    auto sum = x_real;
    for (int i = 0; i < 100; ++i)
        sum = operator_of("+", add_tag, {real_sort, real_sort}, real_sort, {sum, x_real});
    auto sum_rendering = text(sum);
    if (!sum_rendering.second || sum_rendering.first.rfind("holds((+ (+ (+ ", 0) != 0 ||
        !contains(sum_rendering.first, "(+:Real <...depth> <...depth>)")) {
        std::cerr << "readable a cut argument left the sum without its sort: " << sum_rendering.first << '\n';
        ok = false;
    }
    auto nested_sort = [&](int levels) {
        auto result = bool_sort;
        for (int i = 0; i < levels; ++i)
            result = array({int_sort}, result);
        return result;
    };
    auto store_over = [&](Z3AstTheory_sort sort_value) {
        return app(declaration("store", {sort_value}, sort_value, store_tag), {variable(0, sort_value)});
    };
    expect("store over a moderately nested sort", shown(store_over(nested_sort(3))),
           "holds((store #0:(Array Int (Array Int (Array Int Bool)))))");
    auto deep_store = text(store_over(nested_sort(100)));
    if (!deep_store.second || deep_store.first.rfind("holds((store:(Array Int (Array Int ", 0) != 0 ||
        !contains(deep_store.first, "<...depth>")) {
        std::cerr << "readable sorts nested beyond the limit were compared: " << deep_store.first << '\n';
        ok = false;
    }
    auto shared_sort = int_sort;
    for (int i = 0; i < 40; ++i)
        shared_sort = array({shared_sort, shared_sort}, bool_sort);
    auto shared_started = std::chrono::steady_clock::now();
    auto shared_store = text(store_over(shared_sort));
    if (!shared_store.second || shared_store.first.rfind("holds((store:(Array ", 0) != 0 ||
        std::chrono::steady_clock::now() - shared_started >= std::chrono::seconds(5)) {
        std::cerr << "readable sorts sharing their parts were compared without a budget: " << shared_store.first << '\n';
        ok = false;
    }
    auto nested = bool_sort;
    for (int i = 0; i < 100; ++i)
        nested = array({int_sort}, nested);
    auto nested_rendering = text(app(declaration("const", {bool_sort}, nested, const_tag), {truth}));
    if (!nested_rendering.second || nested_rendering.first.size() >= 700 ||
        nested_rendering.first.rfind("holds((const:(Array Int (Array Int ", 0) != 0) {
        std::cerr << "readable a deeply nested array range was not cut with a marker: " << nested_rendering.first << '\n';
        ok = false;
    }
    // chains of heads: an omitted range follows from what is printed; what is cut, not compared or does not print its own sort keeps it
    auto over_bv = shown(const_array({bv8}, int_sort, zero));
    expect("constant array over a bit-vector domain", over_bv, "holds((const:(Array BV8 Int) 0))");
    if (over_bv == over_int || over_bv == over_real) {
        std::cerr << "readable constant arrays over Int, Real and bit-vector domains read alike\n";
        ok = false;
    }
    auto numeral_of = [&](Z3AstTheory_sort range, int64_t n) { return constant("numeral", range, Z3Cherry_rational_op, {z(n), z(1)}); };
    expect("integral Real numeral under a sum",
           shown(operator_of("+", add_tag, {real_sort, real_sort}, real_sort, {numeral_of(real_sort, 2), x_real})),
           "holds((+ 2:Real #1:Real))");
    expect("integer literal under a sum",
           shown(operator_of("+", add_tag, {int_sort, int_sort}, int_sort, {numeral_of(int_sort, 2), y_int})),
           "holds((+ 2 #2:Int))");
    expect("select of a store of a constant array",
           shown(app(declaration("select", {arrays, int_sort}, int_sort, select_tag), {store_of(const_array({int_sort}, int_sort, zero)), zero})),
           "holds((select:Int (store (const:(Array Int Int) 0) 0 0) 0))");
    auto ite_int = [&](Z3AstTheory_expr a, Z3AstTheory_expr b) {
        return operator_of("ite", ite_tag, {bool_sort, int_sort, int_sort}, int_sort, {c_bool, a, b});
    };
    expect("nested conditionals", shown(ite_int(ite_int(zero, y_int), y_int)),
           "holds((ite:Int #3:Bool (ite:Int #3:Bool 0 #2:Int) #2:Int))");
    auto lambda = quantifier(Z3ASTTHEORY_LAMBDA_K, {int_sort}, arrays, variable(0, int_sort));
    expect("a lambda argument does not print its sort", shown(store_of(lambda)),
           "holds((store:(Array Int Int) (lambda [Int] #0:Int) 0 0))");
    auto int_sum = y_int;
    for (int i = 0; i < 100; ++i)
        int_sum = operator_of("+", add_tag, {int_sort, int_sort}, int_sort, {int_sum, y_int});
    auto converted = text(operator_of("to_real", to_real_tag, {int_sort}, real_sort, {int_sum}));
    if (!converted.second || converted.first.rfind("holds((to_real:Real (+ (+ ", 0) != 0 ||
        !contains(converted.first, "(+:Int <...depth> <...depth>)")) {
        std::cerr << "readable a conversion of a cut sum lost a sort: " << converted.first << '\n';
        ok = false;
    }
    auto real_sum = operator_of("+", add_tag, {real_sort, real_sort}, real_sort, {x_real, x_real});
    auto node_limited = [&](int fillers) {
        std::vector<Z3AstTheory_expr> arguments(fillers, zero);
        arguments.push_back(real_sum);
        return text(app(declaration("decl!8:h", {}, int_sort), arguments));
    };
    auto at_limit = node_limited(998), below_limit = node_limited(997);
    if (!at_limit.second || !contains(at_limit.first, "(+:Real <...nodes>")) {
        std::cerr << "readable a head whose argument is cut at the node limit lost its sort\n";
        ok = false;
    }
    if (!below_limit.second || !contains(below_limit.first, "(+ #1:Real <...nodes>")) {
        std::cerr << "readable a head whose first argument is printed printed a range\n";
        ok = false;
    }
    auto long_sort = [&](size_t length) { return base(std::string(length, 'S')); };
    auto long_store = shown(store_over(long_sort(5000)));
    if (long_store.rfind("holds((store:|S", 0) != 0 || !contains(long_store, "<4904 more bytes>")) {
        std::cerr << "readable sort names beyond the comparison limit were compared: " << long_store << '\n';
        ok = false;
    }
    if (shown(store_over(long_sort(100))).rfind("holds((store #0:|S", 0) != 0) {
        std::cerr << "readable equal sort names of 100 bytes were not recognized\n";
        ok = false;
    }
    std::vector<Z3AstTheory_expr> many_reals(3001, x_real);
    auto clipped = text(operator_of("+", add_tag, {real_sort, real_sort}, real_sort, many_reals));
    if (!clipped.second || clipped.first.rfind("holds((+ #1:Real #1:Real", 0) != 0 ||
        clipped.first.size() < 10 || clipped.first.compare(clipped.first.size() - 10, 10, "<...chars>") != 0) {
        std::cerr << "readable output clipping hid where the text ends\n";
        ok = false;
    }

    // the report, on readable_report itself
    auto five = constant("numeral", int_sort, Z3Cherry_rational_op, {z(5), z(1)});
    auto x = constant("decl!3:x", int_sort);
    auto conclusion = app(declaration("=", {int_sort, int_sort}, bool_sort, eq_tag), {x, five});
    auto lines = [](std::initializer_list<std::string> rows) {
        std::string result;
        for (auto const& row : rows)
            result += row + "\n";
        return result;
    };
    auto report = [&](unsigned query, std::string const& verdict, Z3ProofDocument_document_Mk_document_s const& document,
                      Z3ProofDocument_document_diagnostic const& diagnostic) {
        return readable_report(query, verdict, document, diagnostic);
    };
    auto const two = z(2);
    // two entries, as in the OCaml golden: node 1 has premise ids #31 #77
    auto leaf = entry_of("th-lemma", conclusion, {z(31), z(77)});
    auto doc = document_of({leaf, leaf});
    auto obligation = [&](std::string const& rule, int64_t index, Z3UnifiedProof_judgment judgment,
                          std::vector<Z3UnifiedProof_judgment> const& premises) {
        return obligation_of(rule, index, two, judgment, premises, conclusion);
    };
    std::vector<Z3UnifiedProof_judgment> const both{holds_of(p), equal_of(x, x)};
    auto checked = [&](std::vector<Z3ProofDocument_unmet_obligation> const& obligations) {
        return report(3, "PARTIAL 2", doc, checked_of(two, obligations));
    };
    expect("checked report", checked({obligation("th-lemma", 1, holds_of(conclusion), both)}),
           lines({"readable\tquery=3\tverdict=PARTIAL 2\tpending=2\tfamilies=1\tshown=1",
                  "readable\tfamily=1/1\trule=th-lemma\tcount=2\tmembers=1\tnode=1\tnode-pending=2",
                  "  node 1: premises: #31 #77", "  premise #31: holds(p#1:Bool)",
                  "  premise #77: equal(x#3:Int, x#3:Int)", "  conclusion: holds((= x#3:Int 5))",
                  "  source formula: same as conclusion", "readable\tend\tquery=3"}));
    require("a differing source formula was hidden",
            contains(checked({obligation("th-lemma", 1, equal_of(x, five), both)}),
                     "  conclusion: equal(x#3:Int, 5)\n  source formula: holds((= x#3:Int 5))\n"));
    auto unmatched = checked({obligation("other", 1, holds_of(conclusion), both)});
    require("premises were attached to a node of another rule",
            contains(unmatched, "  node 1: no source-node mapping (the document entry at this index has another rule or premise "
                                "count): premise ids unavailable\n  premise [0]: holds(p#1:Bool)\n"));
    require("unrelated premise ids were shown", !contains(unmatched, "#31") && !contains(unmatched, "#77"));
    auto miscounted = checked({obligation("th-lemma", 1, holds_of(conclusion), {holds_of(p)})});
    require("premises were attached to a node with another premise count",
            contains(miscounted, "no source-node mapping (the document entry at this index has another rule or premise count)") &&
            !contains(miscounted, "#31"));
    require("an obligation without a document entry got premise ids",
            contains(checked({obligation("th-lemma", 9, holds_of(conclusion), both)}),
                     "  node 9: no source-node mapping (no document entry at this index): premise ids unavailable\n"));
    require("a rejection without a document entry claimed premises",
            contains(report(7, "REJECT", doc, rejected_of(Z3PROOFDOCUMENT_MISSINGPREMISE, 9, std::nullopt)),
                     "  node 9: no source-node mapping (no document entry at this index)\n"));
    std::vector<Z3ProofDocument_unmet_obligation> numbered;
    for (int i = 0; i < 25; ++i) {
        char rule[16];
        std::snprintf(rule, sizeof rule, "rule-%02d", i);
        numbered.push_back(obligation_of(rule, 0, z(i + 1), holds_of(conclusion), both, conclusion));
    }
    auto limited = checked(numbered);
    require("family limit",
            contains(limited, "pending=2\tfamilies=25\tshown=20\n") &&
            contains(limited, "readable\tomitted\tfamilies=5\treason=family-limit\n") &&
            contains(limited, "readable\tfamily=20/25\trule=rule-05\tcount=6\t") && !contains(limited, "rule=rule-04\t"));
    auto heavy = app(declaration("decl!8:h", {}, int_sort), std::vector<Z3AstTheory_expr>(600, x));
    std::vector<Z3UnifiedProof_judgment> const big_premises(8, holds_of(heavy));
    std::vector<Z3ProofDocument_unmet_obligation> big;
    for (int i = 0; i < 6; ++i)
        big.push_back(obligation_of("big-" + std::to_string(i), 1, two, holds_of(heavy), big_premises, heavy));
    auto sized = checked(big);
    require("report size limit",
            sized.size() < readable::max_report_chars + 200 &&
            contains(sized, "readable\tomitted\treason=report-size\nreadable\tend\tquery=3\n"));
    expect("rejected report", report(4, "REJECT", doc, rejected_of(Z3PROOFDOCUMENT_PROOFENTRY, 1, conclusion)),
           lines({"readable\tquery=4\tverdict=REJECT\tstage=proof-entry\tindex=1",
                  "  node 1: rule=th-lemma premises: #31 #77", "  source formula: holds((= x#3:Int 5))",
                  "readable\tend\tquery=4"}));
    expect("rejected report without a node", report(5, "REJECT", doc, rejected_of(Z3PROOFDOCUMENT_MISSINGROOT, std::nullopt, std::nullopt)),
           lines({"readable\tquery=5\tverdict=REJECT\tstage=missing-root\tindex=-", "  source formula: none reported",
                  "readable\tend\tquery=5"}));
    require("a root-stage rejection claimed a proof node",
            !contains(report(6, "REJECT", doc, rejected_of(Z3PROOFDOCUMENT_OPENROOT, 1, std::nullopt)), "  node "));
    // the premise limit, other stages, an accepted proof and huge counts
    std::vector<cherry_int> ids;
    for (int i = 0; i < 10; ++i)
        ids.push_back(z(100 + i));
    auto many = document_of({entry_of("th-lemma", conclusion, ids)});
    std::vector<Z3UnifiedProof_judgment> premises;
    for (int i = 0; i < 10; ++i)
        premises.push_back(i % 2 == 0 ? holds_of(p) : equal_of(x, x));
    expect("premise limit",
           report(1, "PARTIAL 1", many,
                  checked_of(z(1), {obligation_of("th-lemma", 0, z(1), holds_of(conclusion), premises, conclusion)})),
           lines({"readable\tquery=1\tverdict=PARTIAL 1\tpending=1\tfamilies=1\tshown=1",
                  "readable\tfamily=1/1\trule=th-lemma\tcount=1\tmembers=1\tnode=0\tnode-pending=1",
                  "  node 0: premises: #100 #101 #102 #103 #104 #105 #106 #107 ...<2 more>",
                  "  premise #100: holds(p#1:Bool)", "  premise #101: equal(x#3:Int, x#3:Int)",
                  "  premise #102: holds(p#1:Bool)", "  premise #103: equal(x#3:Int, x#3:Int)",
                  "  premise #104: holds(p#1:Bool)", "  premise #105: equal(x#3:Int, x#3:Int)",
                  "  premise #106: holds(p#1:Bool)", "  premise #107: equal(x#3:Int, x#3:Int)",
                  "  ...<2 more premises omitted>", "  conclusion: holds((= x#3:Int 5))",
                  "  source formula: same as conclusion", "readable\tend\tquery=1"}));
    expect("missing-premise rejection names the node and its premise ids",
           report(8, "REJECT", many, rejected_of(Z3PROOFDOCUMENT_MISSINGPREMISE, 0, std::nullopt)),
           lines({"readable\tquery=8\tverdict=REJECT\tstage=missing-premise\tindex=0",
                  "  node 0: rule=th-lemma premises: #100 #101 #102 #103 #104 #105 #106 #107 ...<2 more>",
                  "  source formula: none reported", "readable\tend\tquery=8"}));
    expect("entry rejection without an index",
           report(9, "REJECT", many, rejected_of(Z3PROOFDOCUMENT_PROOFENTRY, std::nullopt, std::nullopt)),
           lines({"readable\tquery=9\tverdict=REJECT\tstage=proof-entry\tindex=-", "  source formula: none reported",
                  "readable\tend\tquery=9"}));
    expect("accepted proof", report(2, "ACCEPT", many, checked_of(z(0), {})),
           lines({"readable\tquery=2\tverdict=ACCEPT\tpending=0\tfamilies=0\tshown=0", "readable\tend\tquery=2"}));
    auto bare = document_of({entry_of("th-lemma", conclusion, {})});
    auto const googol_squared = decimal("1" + std::string(200, '0'));
    expect("huge counts",
           report(1, "PARTIAL", bare,
                  checked_of(googol_squared, {obligation_of("th-lemma", 0, googol_squared, holds_of(conclusion), {}, conclusion)})),
           lines({"readable\tquery=1\tverdict=PARTIAL\tpending=" + huge("+") + "\tfamilies=1\tshown=1",
                  "readable\tfamily=1/1\trule=th-lemma\tcount=" + huge("+") + "\tmembers=1\tnode=0\tnode-pending=" + huge("+"),
                  "  node 0: premises: none", "  conclusion: holds((= x#3:Int 5))", "  source formula: same as conclusion",
                  "readable\tend\tquery=1"}));
    return ok;
}

// Every datum the printer reads, as text: the conclusion, premises, source formula, index and count of each obligation.
std::string rendered_diagnostic(Z3ProofDocument_document_diagnostic const& value) {
    if (value.tag != Z3PROOFDOCUMENT_DOCUMENTCHECKED)
        return "rejected";
    std::string out = "pending=" + integer(value.val.DocumentChecked.pending);
    each<Prims_list__unmet_obligation_Cons_s>(value.val.DocumentChecked.obligations, [&](auto const& obligation) {
        out += "|" + integer(obligation.obligation_index) + ":" + integer(obligation.obligation_count) + ":" +
            readable::judgment_text(obligation.obligation_conclusion).first;
        each<Prims_list__judgment_Cons_s>(obligation.obligation_premises, [&](auto const& premise) {
            out += ";" + readable::judgment_text(premise).first;
        });
        Z3UnifiedProof_judgment holds{};
        holds.tag = Z3UNIFIEDPROOF_HOLDS;
        holds.val.Holds = obligation.obligation_source;
        out += ";source=" + readable::judgment_text(holds).first;
    });
    return out;
}

// The marshaled proof document as text: the rule tag, premise ids and formula of every entry.
std::string rendered_document(Z3ProofDocument_document_Mk_document_s const& doc) {
    std::string out;
    each<Prims_list__entry_Cons_s>(doc.entries, [&](auto const& entry) {
        out += "|" + std::to_string(static_cast<unsigned>(entry.rule.tag)) + "[";
        each<Prims_list__int_Cons_s>(entry.premise_ids, [&](auto id) { out += integer(id) + ","; });
        Z3UnifiedProof_judgment holds{};
        holds.tag = Z3UNIFIEDPROOF_HOLDS;
        holds.val.Holds = entry.formula;
        out += "]" + readable::judgment_text(holds).first;
    });
    return out;
}

// The printer reads a finished diagnostic. On one fixed native proof: diagnosing, checking and the rendered data are the same before
// and after the printer's rendering functions have run over it, and the proof document is not modified. (readable.h does not call
// the checker: tools/test_native_checker.py guards that textually, as the OCaml bridge test counts the hash calls of a check.)
bool readable_same_proof() {
    bool ok = true;
    auto require = [&](char const* label, bool condition) {
        if (!condition) {
            std::cerr << "readable same proof: " << label << '\n';
            ok = false;
        }
    };
    z3::config config;
    config.set("proof", true);
    z3::context context(config);
    z3::solver solver(context);
    auto x = context.real_const("x");
    solver.add(x * x == 2);
    solver.add(x * x * x == 3);
    if (solver.check() != z3::unsat) {
        std::cerr << "readable same proof: expected an UNSAT proof\n";
        return false;
    }
    auto proof = solver.proof();
    NativeSession session(context);
    std::vector<Z3_ast> assertions;
    auto asserted = solver.assertions();
    for (unsigned i = 0; i < asserted.size(); ++i)
        assertions.push_back(asserted[i]);
    auto inputs = list<Prims_list__ast_Cons_s>(assertions);
    auto marshaled = Z3Cherry_marshal(inputs, proof);
    checker_drop_asts(inputs);
    auto const& doc = *reinterpret_cast<Z3ProofDocument_document_Mk_document_s const*>(marshaled.document);
    auto const entries = doc.entries;
    auto const document_before = rendered_document(doc);
    auto first = Z3Cherry_diagnose(false, marshaled);
    require("the proof has no pending obligation", first.tag == Z3PROOFDOCUMENT_DOCUMENTCHECKED &&
            !cherry_is_scalar(first.val.DocumentChecked.obligations));
    auto const rendered = rendered_diagnostic(first);
    require("rendering the diagnostic is not repeatable", rendered_diagnostic(first) == rendered);
    auto checked = Z3Cherry_check(false, marshaled);
    require("the check result differs from the diagnosed pending count",
            first.tag == Z3PROOFDOCUMENT_DOCUMENTCHECKED && checked.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT &&
            cherry_int_eq(checked.val.Some, first.val.DocumentChecked.pending));
    auto second = Z3Cherry_diagnose(false, marshaled);
    require("diagnosing again after rendering gave other data", rendered_diagnostic(second) == rendered);
    require("rendering changed the proof document", rendered_document(doc) == document_before && doc.entries == entries);
    checker_drop_result(checked);
    checker_drop_diagnostic(second);
    checker_drop_diagnostic(first);
    checker_drop_marshaled(marshaled);
    return ok;
}
}

int main() {
    custard_init_globals();
    if (!Z3CherryTests_run()) {
        std::cerr << "Cherry kernel acceptance/rejection regressions failed\n";
        return 1;
    }
    z3::config config;
    config.set("proof", true);
    z3::context context(config);
    z3::solver solver(context);
    auto falsehood = context.bool_val(false);
    auto truth = context.bool_val(true);
    solver.add(falsehood);
    if (solver.check() != z3::unsat)
        return 1;
    auto proof = solver.proof();
    checker::NativeSession session(context);
    {
        std::vector<Z3_ast> assertions(100000, falsehood);
        auto inputs = checker::list<Prims_list__ast_Cons_s>(assertions);
        auto document = Z3Cherry_marshal(inputs, proof);
        checker_drop_asts(inputs);
        bool complete = checker::length<Prims_list__expr_Cons_s>(
            reinterpret_cast<Z3ProofDocument_document_Mk_document_s const*>(document.document)->assertions) == assertions.size();
        checker_drop_marshaled(document);
        if (!complete) {
            std::cerr << "Cherry wide native assertion marshalling regression failed\n";
            return 1;
        }
    }
    for (auto assertion : {falsehood, truth}) {
        auto inputs = checker::list<Prims_list__ast_Cons_s>({assertion});
        auto document = Z3Cherry_marshal(inputs, proof);
        checker_drop_asts(inputs);
        for (bool sorted : {false, true}) {
            auto result = Z3Cherry_check(sorted, document);
            bool accepted = result.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT &&
                cherry_int_eq(result.val.Some, CHERRY_INT_SMALL(0));
            checker_drop_result(result);
            if (accepted != Z3_is_eq_ast(context, assertion, falsehood)) {
                checker_drop_marshaled(document);
                std::cerr << "Cherry native assertion/proof binding regression failed\n";
                return 1;
            }
        }
        checker_drop_marshaled(document);
    }
    // Native flattening of hand-built `ff-pac` DAGs, as in the OCaml bridge tests.
    auto parsed = context.parse_string(
        "(define-sort F () (_ FiniteField 7))(declare-const z F)(assert (= z (as ff3 F)))");
    auto premise = parsed[0];
    auto numeral = premise.arg(1);
    auto P = context.uninterpreted_sort("P");
    auto I = context.int_sort();
    auto input = context.function("ff-input", I, P);
    auto add = context.function("ff-add", P, P, P);
    auto mul = context.function("ff-mul", P, numeral.get_sort(), I, P);
    auto integral = context.function("ff-mul", P, I, I, P);
    auto other = context.function("ff-sub", P, P, P);
    auto pac = context.function("ff-pac", P, P, P, P);
    auto support = context.function("ff-support", I, P);
    auto flatten = [&](z3::expr root, z3::expr p) -> long {
        auto premises = context.function("ff-premises", p.get_sort(), P);
        auto view = checker::view_ff_pac(pac(premises(p), root, support(context.int_val(0))));
        long nodes = view.tag == FSTAR_PERVASIVES_NATIVE_SOME__FF_PAC_VIEW ?
            static_cast<long>(checker::length<Prims_list__ff_pac_node_Cons_s>(view.val.Some.pac_nodes)) : -1;
        checker_drop_ff_pac(view);
        return nodes;
    };
    auto leaf = input(context.int_val(0));
    auto shared = leaf;
    for (int i = 0; i < 60; ++i)
        shared = add(shared, shared);
    auto chain = input(context.int_val(1));
    for (int i = 0; i < 200000; ++i)
        chain = add(chain, leaf);
    bool flattened =
        flatten(mul(add(leaf, input(context.int_val(1))), numeral, context.int_val(2)), premise) == 4 &&
        flatten(shared, premise) == 61 && flatten(chain, premise) == -1 &&
        flatten(input(context.int_val(-1)), premise) == -1 &&
        flatten(input(context.int_val("4294967296")), premise) == -1 &&
        flatten(integral(leaf, context.int_val(3), context.int_val(0)), premise) == -1 &&
        flatten(other(leaf, leaf), premise) == -1 && flatten(leaf, numeral) == -1;
    if (!flattened) {
        std::cerr << "Cherry native finite-field certificate flattening regression failed\n";
        return 1;
    }
    if (!readable_regressions() || !readable_same_proof() || !readable_edge_cases()) {
        std::cerr << "Cherry readable rendering regressions failed\n";
        return 1;
    }
    if (!pretty_regressions()) {
        std::cerr << "Cherry expression-row regressions failed\n";
        return 1;
    }
    std::cout << "Cherry kernel and native acceptance/rejection regressions passed\n";
    return 0;
}
