#include "native.h"
#include "readable.h"

#include <chrono>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

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
           "holds((extract[32,15,8] #0:BV32))");
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
           "holds(|5|[5])");
    expect("bit-vector numeral without a value", text(constant("bv", bv8, bv_numeral_tag, {z(8)})),
           "holds(bv[8])");
    expect("bit-vector numeral with an extra parameter",
           text(constant("bv", bv8, bv_numeral_tag, {z(8), z(255), z(1)})), "holds(bv[8,255,1])");
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
    if (!readable_regressions() || !readable_same_proof()) {
        std::cerr << "Cherry readable rendering regressions failed\n";
        return 1;
    }
    std::cout << "Cherry kernel and native acceptance/rejection regressions passed\n";
    return 0;
}
