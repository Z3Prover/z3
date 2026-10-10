/*++
Copyright (c) 2026 Microsoft Corporation

Abstract:

    AST ID reuse must not depend on the order of completed releases.

--*/
#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/fpa_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "math/polynomial/algebraic_numbers.h"
#include <algorithm>
#include <array>
#include <iostream>
#include <tuple>

static bool check_tuple() {
    ast_manager m;
    unsigned first_id;
    {
        expr_ref a(m.mk_const("a", m.mk_bool_sort()), m);
        expr_ref b(m.mk_const("b", m.mk_bool_sort()), m);
        first_id = a->get_id();
        // Intentionally exercise library-dependent destruction order.
        std::tuple<expr_ref, expr_ref> refs{a, b}; // NOLINT(z3-ast-tuple-order)
        std::cout << "tuple owns AST IDs " << first_id << " and " << b->get_id() << '\n';
        a.reset();
        b.reset();
        // libstdc++ and libc++ destroy these tuple elements in opposite orders.
    }
    expr_ref next(m.mk_const("next", m.mk_bool_sort()), m);
    std::cout << "next AST ID: " << next->get_id() << std::endl;
    return next->get_id() == first_id;
}

using ids = svector<std::pair<unsigned, unsigned>>;

static ids recycle_in_order(std::array<unsigned, 3> const& order) {
    ast_manager m;
    expr_ref a(m.mk_const("a", m.mk_bool_sort()), m);
    expr_ref b(m.mk_const("b", m.mk_bool_sort()), m);
    expr_ref_vector roots(m);
    roots.push_back(a);
    roots.push_back(b);
    roots.push_back(m.mk_and(a, b));
    a.reset();
    b.reset();
    // Include shared children: releasing a parent can also release its operands.
    for (unsigned i : order)
        roots.set(i, nullptr);
    ids result;
    expr_ref_vector keep(m);
    for (unsigned i = 0; i < 4; ++i) {
        expr_ref e(m.mk_fresh_const("next", m.mk_bool_sort()), m);
        result.push_back({e->get_id(), to_app(e)->get_decl()->get_id()});
        keep.push_back(e);
    }
    return result;
}

struct numeral_snapshot {
    unsigned expr_id, decl_id, external_id, hash;
    bool operator==(numeral_snapshot const&) const = default;
};

static numeral_snapshot recycle_numerals(bool algebraic, bool reverse) {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util arith(m);
    fpa_util fp(m);
    auto numeral = [&](int value) -> app* {
        if (algebraic) {
            scoped_anum n(arith.am()), r(arith.am());
            arith.am().set(n, value);
            arith.am().root(n, 2, r);
            return arith.mk_numeral(arith.am(), r, false);
        }
        scoped_mpf n(fp.fm());
        fp.fm().set(n, 8, 24, value);
        return fp.mk_value(n);
    };
    expr_ref a(numeral(2), m);
    expr_ref b(numeral(3), m);
    if (reverse) {
        b.reset();
        a.reset();
    }
    else {
        a.reset();
        b.reset();
    }
    expr_ref next(numeral(5), m);
    func_decl* decl = to_app(next)->get_decl();
    return {next->get_id(), decl->get_id(), decl->get_parameter(0).get_ext_id(), next->hash()};
}

void tst_ast_id_recycling() {
    bool valid = check_tuple();
    std::array<unsigned, 3> order{0, 1, 2};
    ids expected = recycle_in_order(order);
    bool permutations_match = true;
    while (std::next_permutation(order.begin(), order.end())) {
        ids actual = recycle_in_order(order);
        permutations_match &= actual == expected;
    }
    std::cout << "release permutations match: " << permutations_match << '\n';
    valid &= permutations_match;
    for (bool algebraic : {false, true}) {
        auto forward = recycle_numerals(algebraic, false);
        auto reverse = recycle_numerals(algebraic, true);
        std::cout << (algebraic ? "algebraic" : "floating-point")
                  << " external IDs: " << forward.external_id << " / " << reverse.external_id
                  << "; hashes: " << forward.hash << " / " << reverse.hash << std::endl;
        valid &= forward == reverse;
    }
    ENSURE(valid);
}
