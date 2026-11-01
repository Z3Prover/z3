#pragma once

#include "native.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

// Bounded readable rendering of reflected expressions for --readable. The machine diagnostics
// (Fingerprint in main.cpp) are deliberately lossy; this keeps what the checker saw: numeral values,
// bit-vector widths, declaration parameters, array and binder sorts, and declaration identity.
// It mirrors Z3NativeMain.Readable in the OCaml checker. Every limit leaves a "<...>" marker, and
// nothing here feeds back into checking.
namespace checker::readable {

constexpr unsigned max_depth = 48, max_nodes = 1000, max_chars = 4096, max_name_bytes = 96,
    max_digits = 100, max_params = 16, max_families = 20, max_premises = 8, max_report_chars = 131072;

struct Limit {
    char const* reason;
};

struct Text {
    std::string text;
    unsigned nodes = 0;
    bool cut = false;
    void add(std::string_view piece) {
        if (text.size() + piece.size() > max_chars)
            throw Limit{"chars"};
        text += piece;
    }
};

inline std::string_view view(cherry_string value) {
    return {cherry_str_data(value), cherry_str_size(value)};
}

class DigitBounds {
public:
    cherry_int upper, lower;
    DigitBounds() : upper(cherry_int_of_decimal(("1" + std::string(max_digits, '0')).c_str())),
                    lower(cherry_int_neg(upper)) {}
    ~DigitBounds() {
        cherry_dec(upper);
        cherry_dec(lower);
    }
    DigitBounds(DigitBounds const&) = delete;
    DigitBounds& operator=(DigitBounds const&) = delete;
};

// A numeral is compared with 10^max_digits before it is converted: a huge numeral never becomes
// a huge string.
inline std::string integer_text(cherry_int n) {
    static DigitBounds const bounds;
    if (cherry_int_lt(n, bounds.upper) && cherry_int_gt(n, bounds.lower))
        return integer(n);
    return std::string("<") + (cherry_int_lt(n, CHERRY_INT_SMALL(0)) ? "-" : "+") +
        "huge integer: more than " + std::to_string(max_digits) + " digits omitted>";
}

inline bool simple_character(unsigned char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') ||
        std::string_view("~!@$%^&*_-+=<>.?/").find(static_cast<char>(c)) != std::string_view::npos;
}

struct Decoded {
    size_t width;
    bool valid;
    uint32_t scalar;
};

// Strict UTF-8: no overlong forms, surrogates or values above U+10FFFF. An invalid byte has width 1.
inline Decoded decode_utf8(std::string_view text, size_t i) {
    unsigned char lead = text[i];
    if (lead < 0x80)
        return {1, true, lead};
    size_t extra = 0;
    uint32_t scalar = 0, minimum = 0;
    if (lead >= 0xc2 && lead <= 0xdf) { extra = 1; scalar = lead & 0x1f; minimum = 0x80; }
    else if (lead >= 0xe0 && lead <= 0xef) { extra = 2; scalar = lead & 0x0f; minimum = 0x800; }
    else if (lead >= 0xf0 && lead <= 0xf4) { extra = 3; scalar = lead & 0x07; minimum = 0x10000; }
    else return {1, false, 0};
    if (i + extra >= text.size())
        return {1, false, 0};
    for (size_t k = 1; k <= extra; ++k) {
        unsigned char next = text[i + k];
        if ((next & 0xc0) != 0x80)
            return {1, false, 0};
        scalar = (scalar << 6) | (next & 0x3f);
    }
    if (scalar < minimum || scalar > 0x10ffff || (scalar >= 0xd800 && scalar <= 0xdfff))
        return {1, false, 0};
    return {extra + 1, true, scalar};
}

// SMT-LIB symbol: simple when possible, otherwise |quoted| with \xNN for control, invalid-UTF-8,
// '|' and '\' bytes. Long names are cut at max_name_bytes.
inline std::string symbol(std::string_view name) {
    size_t shown = std::min<size_t>(name.size(), max_name_bytes);
    bool simple = shown > 0 && !(name[0] >= '0' && name[0] <= '9');
    for (size_t i = 0; i < shown && simple; ++i)
        simple = simple_character(static_cast<unsigned char>(name[i]));
    if (simple && shown == name.size())
        return std::string(name);
    std::string quoted = "|";
    size_t position = 0;
    while (position < shown) {
        auto decoded = decode_utf8(name, position);
        bool plain = decoded.valid && decoded.scalar >= 0x20 && decoded.scalar != 0x7f &&
            (decoded.scalar < 0x80 || decoded.scalar >= 0xa0) && decoded.scalar != 0x7c &&
            decoded.scalar != 0x5c;
        if (plain)
            quoted += name.substr(position, decoded.width);
        else
            for (size_t j = 0; j < decoded.width; ++j) {
                char escape[8];
                std::snprintf(escape, sizeof escape, "\\x%02x",
                              static_cast<unsigned>(static_cast<unsigned char>(name[position + j])));
                quoted += escape;
            }
        position += decoded.width;
    }
    if (position < name.size())
        quoted += "...<" + std::to_string(name.size() - position) + " more bytes>";
    return quoted + "|";
}

// The native bridge names an opaque declaration "decl!ID:NAME" and a non-builtin sort
// "sort!ID:NAME"; they are shown as NAME#ID, which keeps same-named symbols apart.
inline bool identified(std::string_view prefix, std::string_view name, size_t& first,
                       std::string_view& id) {
    size_t start = prefix.size() + 1;
    if (name.size() <= start || name.substr(0, prefix.size()) != prefix || name[prefix.size()] != '!')
        return false;
    size_t stop = std::min(name.size(), start + 21), colon = start;
    while (colon < stop && name[colon] != ':')
        ++colon;
    if (colon == start || colon >= stop)
        return false;
    for (size_t i = start; i < colon; ++i)
        if (name[i] < '0' || name[i] > '9')
            return false;
    first = colon + 1;
    id = name.substr(start, colon - start);
    return true;
}

inline void sort_text(Text& out, Z3AstTheory_sort sort, unsigned depth) {
    if (cherry_tag(sort) == Z3ASTTHEORY_BASESORT) {
        auto name = view(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(sort)->name);
        size_t first = 0;
        std::string_view id;
        out.add(identified("sort", name, first, id) ? symbol(name.substr(first)) + "#" + std::string(id)
                                                    : symbol(name));
        return;
    }
    if (!depth) {
        out.cut = true;
        out.add("<...depth>");
        return;
    }
    auto* array = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(sort);
    out.add("(Array");
    each<Prims_list__sort_Cons_s>(array->domain, [&](auto domain) {
        out.add(" ");
        sort_text(out, domain, depth - 1);
    });
    out.add(" ");
    sort_text(out, array->range, depth - 1);
    out.add(")");
}

inline bool is_int_sort(Z3AstTheory_sort sort) {
    return cherry_tag(sort) == Z3ASTTHEORY_BASESORT &&
        view(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(sort)->name) == "Int";
}

// F* Z3BvLemma.op_numeral; the extracted checker does not export it, unlike the datatype tags.
// tools/test_native_checker.py compares it with the F* source.
inline cherry_int bv_numeral_op() { return CHERRY_INT_SMALL(108); }

inline std::string_view datatype_marker(cherry_int k) {
    if (cherry_int_eq(k, Z3Cherry_constructor_op)) return "@constructor";
    if (cherry_int_eq(k, Z3Cherry_recognizer_op)) return "@recognizer";
    if (cherry_int_eq(k, Z3Cherry_accessor_op)) return "@accessor";
    return "";
}

inline void parameters_text(Text& out, std::vector<cherry_int> const& values) {
    if (values.empty())
        return;
    out.add("[");
    for (size_t i = 0; i < values.size() && i < max_params; ++i) {
        if (i)
            out.add(",");
        out.add(integer_text(values[i]));
    }
    if (values.size() > max_params)
        out.add(",<" + std::to_string(values.size() - max_params) + " more>");
    out.add("]");
}

inline bool is_bool_sort(Z3AstTheory_sort sort) {
    return cherry_tag(sort) == Z3ASTTHEORY_BASESORT &&
        view(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(sort)->name) == "Bool";
}

inline Z3AstTheory_sort sort_of(Z3AstTheory_expr value) {
    switch (cherry_tag(value)) {
    case Z3ASTTHEORY_VAR: return reinterpret_cast<Z3AstTheory_expr_Var_s*>(value)->s;
    case Z3ASTTHEORY_APP: return reinterpret_cast<Z3AstTheory_expr_App_s*>(value)->decl.range;
    case Z3ASTTHEORY_QUANTIFIER: return reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(value)->qsort;
    default: throw NativeError("Invalid extracted expression tag");
    }
}

constexpr size_t max_compared_name_bytes = 4096;

// Sorts are equal if they are the same name or the same array of equal sorts. The comparison is bounded like the rendering (depth,
// nodes, name bytes): when it cannot be completed the sorts count as different, which only prints more.
inline bool same_sort(Z3AstTheory_sort a, Z3AstTheory_sort b, unsigned depth, unsigned& budget) {
    if (!budget)
        return false;
    --budget;
    if (!depth)
        return false;
    bool a_base = cherry_tag(a) == Z3ASTTHEORY_BASESORT, b_base = cherry_tag(b) == Z3ASTTHEORY_BASESORT;
    if (a_base != b_base)
        return false;
    if (a_base) {
        auto x = view(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(a)->name);
        auto y = view(reinterpret_cast<Z3AstTheory_sort_BaseSort_s*>(b)->name);
        return x.size() <= max_compared_name_bytes && x == y;
    }
    auto* left = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(a);
    auto* right = reinterpret_cast<Z3AstTheory_sort_ArraySort_s*>(b);
    auto x = left->domain, y = right->domain;
    while (!cherry_is_scalar(x) && !cherry_is_scalar(y)) {
        auto* cx = reinterpret_cast<Prims_list__sort_Cons_s*>(x);
        auto* cy = reinterpret_cast<Prims_list__sort_Cons_s*>(y);
        if (!same_sort(cx->hd, cy->hd, depth - 1, budget))
            return false;
        x = cx->tl;
        y = cy->tl;
    }
    return cherry_is_scalar(x) && cherry_is_scalar(y) && same_sort(left->range, right->range, depth - 1, budget);
}

inline bool same_sort(Z3AstTheory_sort a, Z3AstTheory_sort b) {
    unsigned budget = max_nodes;
    return same_sort(a, b, max_depth, budget);
}

// A rational numeral shows its value (and its sort unless Int), a bit-vector numeral
// (_ bvVALUE WIDTH). Every other head is NAME, followed by [reflected integer parameters]; an
// uninterpreted head is NAME#ID (or NAME#- without a native id) and a datatype operation carries
// @constructor, @recognizer or @accessor, each with its range sort after ':', so neither can
// be mistaken for a builtin connective that shares its name. Every other interpreted head also
// shows its range after ':', for example (const:(Array Int Int) 0), (select:Int a i) or
// (extract[32,15,8]:BV8 x), because the arguments do not always carry it (the domain sorts of a
// constant array occur nowhere in its arguments), except where the range is printed anyway or
// needs no printing: Bool (connectives and predicates: an interpreted head without a range is
// Bool) and the sort of the first argument, which that argument prints (+ * bvadd store, as in
// SMT-LIB). [implied] says whether the range is the first argument's sort and that argument
// prints its own: it is false when the argument would be cut by the depth or the node limit,
// is a quantifier (a lambda prints its binder sorts, not its own sort), or the comparison was
// not completed.
template<class Implied>
inline void head_text(Text& out, Z3AstTheory_func_decl const& decl, Implied implied) {
    std::vector<cherry_int> values;
    each<Prims_list__int_Cons_s>(decl.int_params, [&](auto n) { values.push_back(n); });
    bool interpreted = decl.interp.tag == FSTAR_PERVASIVES_NATIVE_SOME__INT;
    auto interp_is = [&](cherry_int tag) { return interpreted && cherry_int_eq(decl.interp.val.Some, tag); };
    if (values.size() == 2 && interp_is(Z3Cherry_rational_op)) {
        out.add(integer_text(values[0]));
        if (!cherry_int_eq(values[1], CHERRY_INT_SMALL(1)))
            out.add("/" + integer_text(values[1]));
        if (!is_int_sort(decl.range)) {
            out.add(":");
            sort_text(out, decl.range, max_depth);
        }
        return;
    }
    if (values.size() == 2 && interp_is(bv_numeral_op())) {
        out.add("(_ bv" + integer_text(values[1]) + " " + integer_text(values[0]) + ")");
        return;
    }
    auto name = view(decl.decl_name);
    std::string head;
    if (interpreted)
        head = symbol(name) + std::string(datatype_marker(decl.interp.val.Some));
    else {
        size_t first = 0;
        std::string_view id;
        head = identified("decl", name, first, id) ? symbol(name.substr(first)) + "#" + std::string(id)
                                                   : symbol(name) + "#-";
    }
    out.add(head);
    parameters_text(out, values);
    bool annotated = !interpreted || !datatype_marker(decl.interp.val.Some).empty() ||
        (!is_bool_sort(decl.range) && !implied());
    if (annotated) {
        out.add(":");
        sort_text(out, decl.range, max_depth);
    }
}

inline void expression_text(Text& out, Z3AstTheory_expr value, unsigned depth) {
    if (!depth) {
        out.cut = true;
        out.add("<...depth>");
        return;
    }
    if (out.nodes >= max_nodes)
        throw Limit{"nodes"};
    ++out.nodes;
    switch (cherry_tag(value)) {
    case Z3ASTTHEORY_VAR: {
        auto* variable = reinterpret_cast<Z3AstTheory_expr_Var_s*>(value);
        out.add("#" + integer_text(variable->idx) + ":");
        sort_text(out, variable->s, max_depth);
        return;
    }
    case Z3ASTTHEORY_QUANTIFIER: {
        auto* quantified = reinterpret_cast<Z3AstTheory_expr_Quantifier_s*>(value);
        out.add(std::string("(") + (quantified->qk == Z3ASTTHEORY_FORALL_K ? "forall" :
            quantified->qk == Z3ASTTHEORY_EXISTS_K ? "exists" : "lambda") + " [");
        bool first = true;
        each<Prims_list__sort_Cons_s>(quantified->bound_sorts, [&](auto sort) {
            if (!std::exchange(first, false))
                out.add(" ");
            sort_text(out, sort, max_depth);
        });
        out.add("] ");
        expression_text(out, quantified->body, depth - 1);
        out.add(")");
        return;
    }
    case Z3ASTTHEORY_APP: {
        auto* app = reinterpret_cast<Z3AstTheory_expr_App_s*>(value);
        if (cherry_is_scalar(app->args)) {
            head_text(out, app->decl, [] { return false; });
            return;
        }
        out.add("(");
        head_text(out, app->decl, [&] {
            auto first = reinterpret_cast<Prims_list__expr_Cons_s*>(app->args)->hd;
            return depth >= 2 && out.nodes < max_nodes && cherry_tag(first) != Z3ASTTHEORY_QUANTIFIER &&
                same_sort(app->decl.range, sort_of(first));
        });
        each<Prims_list__expr_Cons_s>(app->args, [&](auto argument) {
            out.add(" ");
            expression_text(out, argument, depth - 1);
        });
        out.add(")");
        return;
    }
    default: throw NativeError("Invalid extracted expression tag");
    }
}

inline void judgment_into(Text& out, Z3UnifiedProof_judgment const& value) {
    switch (value.tag) {
    case Z3UNIFIEDPROOF_HOLDS:
        out.add("holds(");
        expression_text(out, value.val.Holds, max_depth);
        out.add(")");
        return;
    case Z3UNIFIEDPROOF_EQUAL:
        out.add("equal(");
        expression_text(out, value.val.Equal.left, max_depth);
        out.add(", ");
        expression_text(out, value.val.Equal.right, max_depth);
        out.add(")");
        return;
    case Z3UNIFIEDPROOF_OBSERVATIONAL:
        out.add("observational(");
        expression_text(out, value.val.Observational.left, max_depth);
        out.add(", ");
        expression_text(out, value.val.Observational.right, max_depth);
        out.add(")");
        return;
    default: throw NativeError("Invalid extracted judgment tag");
    }
}

// The bounded text of [write], and whether any limit cut it short.
using Rendered = std::pair<std::string, bool>;

template<class Write>
inline Rendered render(Write write) {
    Text out;
    try {
        write(out);
    }
    catch (Limit const& limit) {
        out.cut = true;
        out.text += std::string("<...") + limit.reason + ">";
    }
    return {std::move(out.text), out.cut};
}

inline Rendered judgment_text(Z3UnifiedProof_judgment const& value) {
    return render([&](Text& out) { judgment_into(out, value); });
}
}
