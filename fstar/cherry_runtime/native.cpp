#include "native.h"

#include <algorithm>
#include <cctype>
#include <unordered_map>
#include <utility>

namespace checker {
static thread_local NativeSession* active = nullptr;

NativeSession::NativeSession(z3::context& context) : previous(active), context(context) {
    active = this;
}

NativeSession::~NativeSession() {
    for (auto ast : retained)
        Z3_dec_ref(context, ast);
    active = previous;
}

Z3_ast NativeSession::keep(Z3_ast ast) {
    context.check_error();
    if (!ast)
        throw NativeError("Missing native AST");
    if (retained.insert(ast).second)
        Z3_inc_ref(context, ast);
    return ast;
}

static z3::context& context() {
    if (!active)
        throw NativeError("Native operation outside a proof-checking session");
    return active->context;
}

static Z3_ast keep(Z3_ast ast) { return active->keep(ast); }
static Z3_sort keep_sort(Z3_sort sort) {
    keep(Z3_sort_to_ast(context(), sort));
    return sort;
}

std::string text(cherry_string value) {
    return {cherry_str_data(value), cherry_str_size(value)};
}

std::string integer(cherry_int value) {
    auto rendered = cherry_string_of_int(value);
    auto result = text(rendered);
    cherry_dec(rendered);
    return result;
}

[[noreturn]] void fail(cherry_string message) {
    throw NativeError(text(message));
}

static cherry_string string(std::string const& value) {
    return cherry_str_of_bytes(value.data(), value.size());
}

static cherry_int number(uint64_t value) { return cherry_int_of_u64(value); }

template<class T>
static T checked(T value) {
    context().check_error();
    return value;
}

static std::string symbol(Z3_symbol value) {
    auto& c = context();
    return Z3_get_symbol_kind(c, value) == Z3_INT_SYMBOL ?
        std::to_string(Z3_get_symbol_int(c, value)) : Z3_get_symbol_string(c, value);
}

static std::string unique(char const* prefix, unsigned id, std::string const& name) {
    return std::string(prefix) + "!" + std::to_string(id) + ":" + name;
}

static Rational rational(std::string value) {
    auto slash = value.find('/');
    std::string numerator = value.substr(0, slash);
    std::string denominator = slash == std::string::npos ? "1" : value.substr(slash + 1);
    auto dot = numerator.find('.');
    if (dot != std::string::npos && slash == std::string::npos) {
        denominator.append(numerator.size() - dot - 1, '0');
        numerator.erase(dot, 1);
    }
    auto decimal = [](std::string const& s) {
        size_t first = !s.empty() && s[0] == '-' ? 1 : 0;
        return first < s.size() && std::all_of(s.begin() + first, s.end(),
            [](unsigned char c) { return c >= '0' && c <= '9'; });
    };
    if (!decimal(numerator) || !decimal(denominator) ||
        denominator[0] == '-' || denominator.find_first_not_of('0') == std::string::npos)
        throw NativeError("Invalid native rational: " + value);
    return {cherry_int_of_decimal(numerator.c_str()), cherry_int_of_decimal(denominator.c_str())};
}

static std::vector<Z3_ast> arguments(Z3_ast ast) {
    auto& c = context();
    if (!Z3_is_app(c, ast))
        throw NativeError("Native object is not an application");
    auto app = Z3_to_app(c, ast);
    std::vector<Z3_ast> result;
    for (unsigned i = 0, n = Z3_get_app_num_args(c, app); i < n; ++i)
        result.push_back(keep(Z3_get_app_arg(c, app, i)));
    return result;
}

static std::vector<Z3_sort> bound_sorts(Z3_ast ast) {
    auto& c = context();
    std::vector<Z3_sort> result;
    for (unsigned i = 0, n = Z3_get_quantifier_num_bound(c, ast); i < n; ++i)
        result.push_back(keep_sort(Z3_get_quantifier_bound_sort(c, ast, i)));
    return result;
}

static Z3_decl_kind kind(Z3_ast ast) {
    auto& c = context();
    if (!Z3_is_app(c, ast))
        throw NativeError("Native object is not an application");
    return Z3_get_decl_kind(c, Z3_get_app_decl(c, Z3_to_app(c, ast)));
}

static Z3Native_operator operator_of(Z3_decl_kind kind) {
    switch (kind) {
#define OP(native, logical) case Z3_OP_##native: return Z3NATIVE_##logical
    OP(NOT, NOT); OP(AND, AND); OP(OR, OR); OP(IMPLIES, IMPLIES); OP(EQ, EQ);
    OP(OEQ, OEQ); OP(TRUE, TRUE); OP(FALSE, FALSE); OP(ITE, ITE); OP(XOR, XOR);
    OP(DISTINCT, DISTINCT); OP(SELECT, SELECT); OP(STORE, STORE); OP(ARRAY_EXT, ARRAYEXT);
    OP(BAND, BVAND); OP(BOR, BVOR); OP(BXOR, BVXOR); OP(BNOT, BVNOT);
    OP(BADD, BVADD); OP(BMUL, BVMUL); OP(BSUB, BVSUB); OP(BNEG, BVNEG);
    OP(BUDIV, BVUDIV); OP(BUREM, BVUREM); OP(EXTRACT, BVEXTRACT);
    OP(CONCAT, BVCONCAT); OP(MKBV, BVMKBV); OP(ULT, BVULT); OP(ULEQ, BVULE);
    OP(UGEQ, BVUGE); OP(CONST_ARRAY, CONSTARRAY); OP(DT_CONSTRUCTOR, DATATYPECONSTRUCTOR);
    OP(DT_RECOGNISER, DATATYPERECOGNIZER); OP(DT_IS, DATATYPERECOGNIZER);
    OP(DT_ACCESSOR, DATATYPEACCESSOR); OP(SEQ_CONCAT, CONCAT); OP(ADD, ADD); OP(MUL, MUL);
    OP(SUB, SUB); OP(UMINUS, SUB); OP(DIV, DIV); OP(IDIV, IDIV); OP(MOD, MOD);
    OP(LE, LE); OP(LT, LT); OP(GE, GE); OP(GT, GT); OP(TO_REAL, TOREAL);
    OP(ANUM, RATIONAL); OP(BNUM, BVNUMERAL);
#undef OP
    default: return Z3NATIVE_OPAQUE;
    }
}

static std::vector<cherry_int> datatype_parameters(Z3_func_decl decl, Z3Native_operator op) {
    auto& c = context();
    auto id = [&](Z3_func_decl d) { return number(Z3_get_func_decl_id(c, d)); };
    auto sort_id = [&](Z3_sort s) { return number(Z3_get_sort_id(c, s)); };
    if (op == Z3NATIVE_DATATYPECONSTRUCTOR)
        return {sort_id(Z3_get_range(c, decl)), id(decl), number(Z3_get_domain_size(c, decl))};
    if (op == Z3NATIVE_DATATYPERECOGNIZER) {
        if (Z3_get_decl_num_parameters(c, decl) != 1 ||
            Z3_get_decl_parameter_kind(c, decl, 0) != Z3_PARAMETER_FUNC_DECL)
            throw NativeError("Malformed native datatype recognizer");
        auto constructor = Z3_get_decl_func_decl_parameter(c, decl, 0);
        return {sort_id(Z3_get_range(c, constructor)), id(constructor)};
    }
    auto owner = Z3_get_domain(c, decl, 0);
    for (unsigned i = 0, n = Z3_get_datatype_sort_num_constructors(c, owner); i < n; ++i) {
        auto constructor = Z3_get_datatype_sort_constructor(c, owner, i);
        for (unsigned j = 0, arity = Z3_get_domain_size(c, constructor); j < arity; ++j)
            if (Z3_is_eq_func_decl(c, decl, Z3_get_datatype_sort_constructor_accessor(c, owner, i, j)))
                return {sort_id(owner), id(constructor), number(j)};
    }
    throw NativeError("Native datatype accessor has no owning constructor");
}

static std::vector<cherry_int> parameters(Z3_func_decl decl, Z3_sort range, Z3Native_operator op) {
    auto& c = context();
    auto width = [&](Z3_sort s) { return number(Z3_get_bv_sort_size(c, s)); };
    switch (op) {
    case Z3NATIVE_BVAND: case Z3NATIVE_BVOR: case Z3NATIVE_BVXOR: case Z3NATIVE_BVNOT:
    case Z3NATIVE_BVADD: case Z3NATIVE_BVMUL: case Z3NATIVE_BVSUB: case Z3NATIVE_BVNEG:
    case Z3NATIVE_BVUDIV: case Z3NATIVE_BVUREM: case Z3NATIVE_BVNUMERAL: case Z3NATIVE_BVMKBV:
        return {width(range)};
    case Z3NATIVE_BVULT: case Z3NATIVE_BVULE: case Z3NATIVE_BVUGE:
        if (Z3_get_domain_size(c, decl) != 2)
            throw NativeError("Malformed native unsigned comparison");
        return {width(Z3_get_domain(c, decl, 0))};
    case Z3NATIVE_BVEXTRACT:
        if (Z3_get_decl_num_parameters(c, decl) != 2 || Z3_get_domain_size(c, decl) != 1 ||
            Z3_get_decl_parameter_kind(c, decl, 0) != Z3_PARAMETER_INT ||
            Z3_get_decl_parameter_kind(c, decl, 1) != Z3_PARAMETER_INT)
            throw NativeError("Malformed native bit-vector extraction");
        return {width(Z3_get_domain(c, decl, 0)),
            cherry_int_of_i64(Z3_get_decl_int_parameter(c, decl, 0)),
            cherry_int_of_i64(Z3_get_decl_int_parameter(c, decl, 1))};
    case Z3NATIVE_BVCONCAT: {
        std::vector<cherry_int> result;
        for (unsigned i = 0, n = Z3_get_domain_size(c, decl); i < n; ++i)
            result.push_back(width(Z3_get_domain(c, decl, i)));
        return result;
    }
    case Z3NATIVE_DATATYPECONSTRUCTOR: case Z3NATIVE_DATATYPERECOGNIZER:
    case Z3NATIVE_DATATYPEACCESSOR:
        return datatype_parameters(decl, op);
    default: return {};
    }
}

static Z3Native_sort_view view_sort(Z3_sort sort) {
    auto& c = context();
    Z3Native_sort_view result{};
    result.tag = Z3NATIVE_BASE;
    auto name = symbol(Z3_get_sort_name(c, sort));
    switch (Z3_get_sort_kind(c, sort)) {
    case Z3_BOOL_SORT: name = "Bool"; break;
    case Z3_INT_SORT: name = "Int"; break;
    case Z3_REAL_SORT: name = "Real"; break;
    case Z3_BV_SORT: name = "BV" + std::to_string(Z3_get_bv_sort_size(c, sort)); break;
    case Z3_SEQ_SORT:
        name = Z3_get_sort_kind(c, Z3_get_seq_sort_basis(c, sort)) == Z3_INT_SORT ?
            "SeqInt" : unique("sort", Z3_get_sort_id(c, sort), name);
        break;
    case Z3_ARRAY_SORT: {
        std::vector<Z3_sort> domains;
        for (unsigned i = 0, n = Z3_get_array_arity(c, sort); i < n; ++i)
            domains.push_back(keep_sort(Z3_get_array_sort_domain_n(c, sort, i)));
        result.tag = Z3NATIVE_ARRAY;
        result.val.Array = {list<Prims_list__native_sort_Cons_s>(domains),
            keep_sort(Z3_get_array_sort_range(c, sort))};
        return result;
    }
    default: name = unique("sort", Z3_get_sort_id(c, sort), name);
    }
    result.val.Base = string(name);
    return result;
}

class LogicalSorts {
    std::unordered_map<unsigned, Z3AstTheory_sort> cache;
public:
    ~LogicalSorts() {
        for (auto const& entry : cache)
            checker_drop_sort(entry.second);
    }
    Z3AstTheory_sort convert(Z3_sort sort) {
        auto id = Z3_get_sort_id(context(), sort);
        auto found = cache.find(id);
        if (found != cache.end()) {
            cherry_inc(found->second);
            return found->second;
        }
        auto view = view_sort(sort);
        Z3AstTheory_sort result;
        if (view.tag == Z3NATIVE_BASE) {
            auto* cell = reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(
                cherry_alloc(sizeof(Z3AstTheory_sort_BaseSort_s), Z3ASTTHEORY_BASESORT));
            cell->name = view.val.Base;
            result = &cell->hdr;
        }
        else {
            std::vector<Z3AstTheory_sort> domains;
            each<Prims_list__native_sort_Cons_s>(view.val.Array.domains,
                [&](Z3_sort s) { domains.push_back(convert(s)); });
            auto domain = list<Prims_list__sort_Cons_s>(domains);
            auto range = convert(view.val.Array.range);
            auto* cell = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(
                cherry_alloc(sizeof(Z3AstTheory_sort_ArraySort_s), Z3ASTTHEORY_ARRAYSORT));
            cell->domain = domain;
            cell->range = range;
            result = &cell->hdr;
            checker_drop_native_sorts(view.val.Array.domains);
        }
        cache.emplace(id, result);
        cherry_inc(result);
        return result;
    }
    Z3AstTheory_func_decl declaration(Z3_func_decl decl) {
        auto& c = context();
        auto op = operator_of(Z3_get_decl_kind(c, decl));
        cherry_int interp;
        switch (op) {
        case Z3NATIVE_DATATYPECONSTRUCTOR: interp = Z3Cherry_constructor_op; break;
        case Z3NATIVE_DATATYPERECOGNIZER: interp = Z3Cherry_recognizer_op; break;
        case Z3NATIVE_DATATYPEACCESSOR: interp = Z3Cherry_accessor_op; break;
        default: throw NativeError("Non-datatype declaration in native datatype signature");
        }
        std::vector<Z3AstTheory_sort> domain;
        for (unsigned i = 0, n = Z3_get_domain_size(c, decl); i < n; ++i)
            domain.push_back(convert(Z3_get_domain(c, decl, i)));
        return {string(symbol(Z3_get_decl_name(c, decl))), list<Prims_list__sort_Cons_s>(domain),
            convert(Z3_get_range(c, decl)),
            some<FStar_Pervasives_Native_option__int>(interp),
            list<Prims_list__int_Cons_s>(datatype_parameters(decl, op))};
    }
};

static bool nested_datatype(Z3_sort sort) {
    auto& c = context();
    switch (Z3_get_sort_kind(c, sort)) {
    case Z3_DATATYPE_SORT: return true;
    case Z3_SEQ_SORT: return nested_datatype(Z3_get_seq_sort_basis(c, sort));
    case Z3_ARRAY_SORT:
        for (unsigned i = 0, n = Z3_get_array_arity(c, sort); i < n; ++i)
            if (nested_datatype(Z3_get_array_sort_domain_n(c, sort, i)))
                return true;
        return nested_datatype(Z3_get_array_sort_range(c, sort));
    default: return false;
    }
}
}

extern "C" cherry_int Z3Native_ast_id(Z3_ast ast) {
    return checker::checked(checker::number(Z3_get_ast_id(checker::context(), ast)));
}

extern "C" cherry_int Z3Native_sort_id(Z3_sort sort) {
    return checker::checked(checker::number(Z3_get_sort_id(checker::context(), sort)));
}

extern "C" Z3Native_sort_view Z3Native_view_sort(Z3_sort sort) {
    return checker::checked(checker::view_sort(sort));
}

extern "C" Z3Native_expression_view Z3Native_view_expression(Z3_ast ast) {
    using namespace checker;
    auto& c = context();
    Z3Native_expression_view result{};
    switch (Z3_get_ast_kind(c, ast)) {
    case Z3_VAR_AST:
        result.tag = Z3NATIVE_VARIABLE;
        result.val.Variable = {number(Z3_get_index_value(c, ast)), keep_sort(Z3_get_sort(c, ast))};
        break;
    case Z3_QUANTIFIER_AST: {
        auto quantifier = Z3_is_quantifier_forall(c, ast) ? Z3ASTTHEORY_FORALL_K :
            Z3_is_quantifier_exists(c, ast) ? Z3ASTTHEORY_EXISTS_K : Z3ASTTHEORY_LAMBDA_K;
        if (quantifier == Z3ASTTHEORY_LAMBDA_K && !Z3_is_lambda(c, ast))
            throw NativeError("Unknown native quantifier kind");
        result.tag = Z3NATIVE_QUANTIFIED;
        result.val.Quantified = {quantifier, list<Prims_list__native_sort_Cons_s>(bound_sorts(ast)),
            keep(Z3_get_quantifier_body(c, ast))};
        break;
    }
    case Z3_APP_AST: case Z3_NUMERAL_AST: {
        auto decl = Z3_get_app_decl(c, Z3_to_app(c, ast));
        auto id = Z3_get_func_decl_id(c, decl);
        auto native_kind = Z3_get_decl_kind(c, decl);
        auto op = operator_of(native_kind);
        auto range = keep_sort(Z3_get_range(c, decl));
        FStar_Pervasives_Native_option__tuple2_int_int numeral{};
        if (op == Z3NATIVE_RATIONAL || op == Z3NATIVE_BVNUMERAL)
            numeral = some<FStar_Pervasives_Native_option__tuple2_int_int>(
                rational(Z3_get_numeral_string(c, ast)));
        std::string name = op == Z3NATIVE_BVNUMERAL ? "bv" :
            op == Z3NATIVE_RATIONAL ? Z3_ast_to_string(c, ast) : symbol(Z3_get_decl_name(c, decl));
        Z3Native_declaration converted{number(id), string(name), string(unique("decl", id, name)),
            op, range, numeral, number(native_kind), list<Prims_list__int_Cons_s>(parameters(decl, range, op))};
        result.tag = Z3NATIVE_APPLICATION;
        result.val.Application = {converted, list<Prims_list__ast_Cons_s>(arguments(ast))};
        break;
    }
    default: throw NativeError("Native object is not an expression");
    }
    return checked(result);
}

extern "C" Z3DatatypeSignature_schema Z3Native_view_datatypes(Prims_list__native_sort roots) {
    using namespace checker;
    auto& c = context();
    LogicalSorts converted;
    std::unordered_set<unsigned> seen;
    std::vector<Z3_sort> todo;
    each<Prims_list__native_sort_Cons_s>(roots, [&](Z3_sort s) { todo.push_back(s); });
    std::reverse(todo.begin(), todo.end());
    std::vector<Z3AstTheory_sort> sorts;
    std::vector<Z3DatatypeSignature_constructor_case> cases;
    while (!todo.empty()) {
        auto sort = todo.back();
        todo.pop_back();
        if (!seen.insert(Z3_get_sort_id(c, sort)).second)
            continue;
        std::vector<Z3_sort> children;
        switch (Z3_get_sort_kind(c, sort)) {
        case Z3_DATATYPE_SORT: {
            auto count = Z3_get_datatype_sort_num_constructors(c, sort);
            if (!count)
                throw NativeError("Native datatype signature has no constructors");
            sorts.push_back(converted.convert(sort));
            for (unsigned i = 0; i < count; ++i) {
                auto constructor = Z3_get_datatype_sort_constructor(c, sort, i);
                std::vector<Z3AstTheory_func_decl> accessors;
                for (unsigned j = 0, n = Z3_get_domain_size(c, constructor); j < n; ++j) {
                    accessors.push_back(converted.declaration(
                        Z3_get_datatype_sort_constructor_accessor(c, sort, i, j)));
                    children.push_back(Z3_get_domain(c, constructor, j));
                }
                cases.push_back({converted.declaration(constructor),
                    converted.declaration(Z3_get_datatype_sort_recognizer(c, sort, i)),
                    list<Prims_list__func_decl_Cons_s>(accessors)});
            }
            break;
        }
        case Z3_ARRAY_SORT:
            for (unsigned i = 0, n = Z3_get_array_arity(c, sort); i < n; ++i)
                children.push_back(Z3_get_array_sort_domain_n(c, sort, i));
            children.push_back(Z3_get_array_sort_range(c, sort));
            break;
        case Z3_SEQ_SORT:
            if (nested_datatype(sort))
                throw NativeError("Nested datatype sequence fields are not supported");
            break;
        default: break;
        }
        todo.insert(todo.end(), children.rbegin(), children.rend());
    }
    return checked(Z3DatatypeSignature_schema{list<Prims_list__sort_Cons_s>(sorts),
        list<Prims_list__constructor_case_Cons_s>(cases)});
}

extern "C" Z3Native_proof_view Z3Native_view_proof(Z3_ast ast) {
    using namespace checker;
    auto& c = context();
    auto args = arguments(ast);
    auto decl = Z3_get_app_decl(c, Z3_to_app(c, ast));
    auto name = symbol(Z3_get_decl_name(c, decl));
    if (args.empty())
        throw NativeError("Native proof has no conclusion: " + name);
    auto conclusion = args.back();
    args.pop_back();
    std::vector<Z3_ast> premises;
    for (auto arg : args)
        if (Z3_get_sort_kind(c, Z3_get_sort(c, arg)) == Z3_UNKNOWN_SORT)
            premises.push_back(arg);
    auto count = Z3_get_decl_num_parameters(c, decl);
    auto parameter_symbol = [&](unsigned i) {
        return Z3_get_decl_parameter_kind(c, decl, i) == Z3_PARAMETER_SYMBOL ?
            symbol(Z3_get_decl_symbol_parameter(c, decl, i)) : std::string();
    };
    auto rational_parameter = [&](unsigned i) -> Rational {
        auto kind = Z3_get_decl_parameter_kind(c, decl, i);
        if (kind == Z3_PARAMETER_RATIONAL)
            return rational(Z3_get_decl_rational_parameter(c, decl, i));
        if (kind == Z3_PARAMETER_INT)
            return {cherry_int_of_i64(Z3_get_decl_int_parameter(c, decl, i)), number(1)};
        throw NativeError("Non-rational native arithmetic coefficient");
    };
    auto hint = name == "th-lemma" && count >= 2 && parameter_symbol(0) == "arith" ?
        parameter_symbol(1) : std::string();
    std::vector<Rational> coefficients;
    bool has_farkas = false;
    if (hint == "farkas" || hint == "bound" || hint == "assign-bounds") {
        has_farkas = true;
        if (hint == "assign-bounds" && premises.empty())
            coefficients.push_back({number(1), number(1)});
        for (unsigned i = 2; i < count; ++i)
            coefficients.push_back(rational_parameter(i));
        if (hint == "assign-bounds" && !premises.empty())
            coefficients.push_back({number(1), number(1)});
    }
    else if (hint == "lp-linear" && count >= 3) {
        has_farkas = true;
        coefficients.push_back({number(0), number(1)});
        for (unsigned i = 3; i < count; ++i)
            coefficients.push_back(rational_parameter(i));
    }
    else if ((hint == "lp-input" || hint == "lp-discharge") && count == 3 &&
             (premises.size() == 1 || premises.size() == 2)) {
        has_farkas = true;
        coefficients.push_back({number(0), number(1)});
        for (size_t i = 0; i < premises.size(); ++i)
            coefficients.push_back({number(1), number(1)});
    }
    Z3Native_proof_view result{};
    auto proof_name = hint == "lp-context" ? "def-axiom" :
        !has_farkas && hint.starts_with("lp-") ? "arith/" + hint : name;
    result.proof_name = string(proof_name);
    result.premises = list<Prims_list__ast_Cons_s>(premises);
    result.conclusion = conclusion;
    if (has_farkas)
        result.farkas = some<FStar_Pervasives_Native_option__list_tuple2_int_int>(
            list<Prims_list__tuple2_int_int_Cons_s>(coefficients));
    if (name == "th-lemma" && count == 3 && parameter_symbol(0) == "arith" &&
        parameter_symbol(1) == "assumed" && Z3_get_decl_parameter_kind(c, decl, 2) == Z3_PARAMETER_SYMBOL)
        result.assumed = some<FStar_Pervasives_Native_option__string>(string(parameter_symbol(2)));
    if (hint.starts_with("lp-")) {
        std::vector<Z3Native_parameter_view> values;
        for (unsigned i = 2; i < count; ++i) {
            Z3Native_parameter_view value{};
            value.tag = Z3NATIVE_PARAMETERUNSUPPORTED;
            auto kind = Z3_get_decl_parameter_kind(c, decl, i);
            if (kind == Z3_PARAMETER_RATIONAL) {
                auto q = rational_parameter(i);
                value.tag = Z3NATIVE_PARAMETERRATIONAL;
                value.val.ParameterRational = {q._1, q._2};
            }
            else if (kind == Z3_PARAMETER_AST) {
                auto ast = keep(Z3_get_decl_ast_parameter(c, decl, i));
                switch (Z3_get_ast_kind(c, ast)) {
                case Z3_APP_AST: case Z3_NUMERAL_AST: case Z3_VAR_AST: case Z3_QUANTIFIER_AST:
                    value.tag = Z3NATIVE_PARAMETEREXPRESSION;
                    value.val.ParameterExpression = ast;
                    break;
                default: break;
                }
            }
            values.push_back(value);
        }
        result.lp_data = some<FStar_Pervasives_Native_option__tuple2_string_list_parameter_view>(
            {string(hint), list<Prims_list__parameter_view_Cons_s>(values)});
    }
    if (Z3_get_decl_kind(c, decl) == Z3_OP_PR_BIND) {
        auto all_args = arguments(ast);
        if (all_args.size() != 1 || !Z3_is_lambda(c, all_args[0]))
            throw NativeError("Malformed native proof binder");
        auto lambda = all_args[0];
        result.binding = some<FStar_Pervasives_Native_option__tuple2_list_native_sort_ast>(
            {list<Prims_list__native_sort_Cons_s>(bound_sorts(lambda)),
             keep(Z3_get_quantifier_body(c, lambda))});
    }
    std::vector<Z3_ast> instantiations;
    if (Z3_get_decl_kind(c, decl) == Z3_OP_PR_QUANT_INST)
        for (unsigned i = 0; i < count; ++i) {
            if (Z3_get_decl_parameter_kind(c, decl, i) != Z3_PARAMETER_AST)
                throw NativeError("Malformed native quantified instance parameter");
            instantiations.push_back(keep(Z3_get_decl_ast_parameter(c, decl, i)));
        }
    result.instantiations = list<Prims_list__ast_Cons_s>(instantiations);
    return checked(result);
}

extern "C" checker::ClauseTrail Z3Native_view_clause_trail(Z3_ast ast) {
    using namespace checker;
    auto& c = context();
    if (kind(ast) != Z3_OP_PR_CLAUSE_TRAIL)
        return {};
    auto args = arguments(ast);
    if (args.empty())
        throw NativeError("Clause proof trail has no conclusion");
    auto conclusion = args.back();
    args.pop_back();
    std::vector<Z3Native_clause_view> entries;
    for (auto entry : args) {
        Z3Native_clause_view value{};
        switch (kind(entry)) {
        case Z3_OP_PR_ASSUMPTION_ADD: value.action = Z3NATIVE_INPUTCLAUSE; break;
        case Z3_OP_PR_LEMMA_ADD: value.action = Z3NATIVE_LEARNEDCLAUSE; break;
        case Z3_OP_PR_TH_ASSUMPTION_ADD: case Z3_OP_PR_TH_LEMMA_ADD:
            value.action = Z3NATIVE_THEORYCLAUSE; break;
        case Z3_OP_PR_REDUNDANT_DEL: value.action = Z3NATIVE_DELETECLAUSE; break;
        default: throw NativeError("Unknown clause proof entry kind");
        }
        auto fields = arguments(entry);
        if (fields.size() == 2 && value.action != Z3NATIVE_DELETECLAUSE)
            value.certificate = some<FStar_Pervasives_Native_option__ast>(fields[0]);
        else if (fields.size() != 1)
            throw NativeError("Malformed clause proof entry");
        auto formula = fields.back();
        if (Z3_get_sort_kind(c, Z3_get_sort(c, formula)) != Z3_BOOL_SORT)
            throw NativeError("Clause proof conclusion is not Boolean");
        std::vector<Z3_ast> literals;
        if (kind(formula) == Z3_OP_OR) {
            literals = arguments(formula);
            if (literals.size() == 1)
                formula = literals[0];
        }
        else if (kind(formula) != Z3_OP_FALSE)
            literals.push_back(formula);
        value.formula = formula;
        value.literals = list<Prims_list__ast_Cons_s>(literals);
        entries.push_back(value);
    }
    return checked(some<ClauseTrail>(
        {list<Prims_list__clause_view_Cons_s>(entries), conclusion}));
}

#include "native_failures.inc"
