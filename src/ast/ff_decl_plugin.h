/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_decl_plugin.h

Abstract:

    Declaration plugin for prime-field (finite field) sorts and values:
    canonical modular numerals, field arithmetic operators, and family
    registration.

Author:

    Romain Soulat

--*/
#pragma once
#include "ast/ast.h"

enum ff_sort_kind { FINITE_FIELD_SORT };
enum ff_op_kind { OP_FF_NUM, OP_FF_ADD, OP_FF_MUL, OP_FF_NEG, OP_FF_BITSUM };

class ff_decl_plugin : public decl_plugin {
    vector<rational> m_checked_moduli;

public:
    decl_plugin *mk_fresh() override {
        return alloc(ff_decl_plugin);
    }
    sort *mk_sort(decl_kind k, unsigned n, parameter const *ps) override;
    func_decl *mk_func_decl(decl_kind k, unsigned n, parameter const *ps, unsigned arity, sort *const *domain,
                            sort *range) override;
    void get_op_names(svector<builtin_name> &names, symbol const &) override;
    void get_sort_names(svector<builtin_name> &names, symbol const &) override;
    bool is_value(app *e) const override {
        return is_app_of(e, m_family_id, OP_FF_NUM);
    }
    bool is_unique_value(app *e) const override {
        return is_value(e);
    }
    bool are_equal(app *a, app *b) const override {
        return a == b;
    }
    bool are_distinct(app *a, app *b) const override {
        return a != b && is_value(a) && is_value(b);
    }
    expr *get_some_value(sort *s) override;
};

class ff_util {
    ast_manager &m;
    family_id m_fid;

public:
    explicit ff_util(ast_manager &m) : m(m), m_fid(m.mk_family_id("ff")) {}
    family_id get_fid() const {
        return m_fid;
    }
    bool is_ff(sort *s) const {
        return s->get_family_id() == m_fid;
    }
    bool is_ff(expr *e) const {
        return is_ff(e->get_sort());
    }
    rational const &modulus(sort *s) const {
        SASSERT(is_ff(s));
        return s->get_parameter(0).get_rational();
    }
    unsigned width(sort *s) const {
        return (modulus(s) - rational(1)).get_num_bits();
    }
    sort *mk_sort(rational const &p) {
        parameter q(p);
        return m.mk_sort(m_fid, FINITE_FIELD_SORT, 1, &q);
    }
    app *mk_numeral(rational const &v, sort *s) const {
        parameter q(mod(v, modulus(s)));
        return m.mk_app(m_fid, OP_FF_NUM, 1, &q, 0, nullptr, s);
    }
    bool is_numeral(expr *e) const {
        return is_app_of(e, m_fid, OP_FF_NUM);
    }
    bool is_numeral(expr *e, rational &v) const {
        if (!is_numeral(e))
            return false;
        v = to_app(e)->get_parameter(0).get_rational();
        return true;
    }
    app *mk_app(decl_kind k, unsigned n, expr *const *args) const {
        return m.mk_app(m_fid, k, n, args);
    }
    app *mk_add(unsigned n, expr *const *args) const {
        return mk_app(OP_FF_ADD, n, args);
    }
    app *mk_add(expr *a, expr *b) const {
        expr *args[2] = {a, b};
        return mk_add(2, args);
    }
    template <typename Vec>
    app *mk_add(Vec const &args) const {
        return mk_add(args.size(), args.data());
    }
    app *mk_mul(unsigned n, expr *const *args) const {
        return mk_app(OP_FF_MUL, n, args);
    }
    app *mk_mul(expr *a, expr *b) const {
        expr *args[2] = {a, b};
        return mk_mul(2, args);
    }
    template <typename Vec>
    app *mk_mul(Vec const &args) const {
        return mk_mul(args.size(), args.data());
    }
    app *mk_neg(expr *a) const {
        return mk_app(OP_FF_NEG, 1, &a);
    }
    app *mk_bitsum(unsigned n, expr *const *args) const {
        return mk_app(OP_FF_BITSUM, n, args);
    }
    template <typename Vec>
    app *mk_bitsum(Vec const &args) {
        return mk_bitsum(args.size(), args.data());
    }
    bool is_add(expr const *e) const {
        return is_app_of(e, m_fid, OP_FF_ADD);
    }
    bool is_mul(expr const *e) const {
        return is_app_of(e, m_fid, OP_FF_MUL);
    }
    bool is_neg(expr const *e) const {
        return is_app_of(e, m_fid, OP_FF_NEG);
    }
    bool is_bitsum(expr const *e) const {
        return is_app_of(e, m_fid, OP_FF_BITSUM);
    }
    MATCH_BINARY(is_add);
    MATCH_BINARY(is_mul);
    MATCH_UNARY(is_neg);

    // true if e is an FF-interpreted operator (add/mul/neg/bitsum/numeral).
    bool is_interp(expr *e) const {
        return is_app(e) && to_app(e)->get_family_id() == m_fid;
    }

    // If e is syntactically a perfect square (a numeral whose integer
    // representative is a perfect square, or a product all of whose symbolic
    // factors have even multiplicity, up to a square constant coefficient),
    // return A such that e=A*A; otherwise return null. The result is built
    // from the original factors and is not canonicalized/sorted: callers
    // that need a canonical form should rewrite the result themselves.
    expr_ref square_root(expr *e) const {
        rational value, root;
        if (is_numeral(e, value)) {
            // An integer square representative is also a square modulo p.
            // Failure here is not a nonresidue test: leave other residues to
            // algebra. In particular, do not discard modular-only square roots.
            if (value.is_int_perfect_square(root))
                return expr_ref(mk_numeral(root, e->get_sort()), m);
            return expr_ref(m);
        }
        if (!is_mul(e) || to_app(e)->get_num_args() > 16)
            return expr_ref(m);
        obj_map<expr, unsigned> powers;
        rational coefficient(1);
        // Binary associative ASTs may hide repeated factors at different
        // depths. Flatten the product, retaining every occurrence: a visited
        // set would incorrectly turn x*x into x and invalidate the square test.
        ptr_vector<expr> pending;
        pending.push_back(e);
        unsigned factor_count = 0;
        while (!pending.empty()) {
            if (!m.inc())
                return expr_ref(m);
            expr *arg = pending.back();
            pending.pop_back();
            if (is_mul(arg)) {
                for (expr *factor : *to_app(arg))
                    pending.push_back(factor);
            }
            else {
                if (++factor_count > 16)
                    return expr_ref(m);
                if (is_numeral(arg, value))
                    coefficient = mod(coefficient * value, modulus(e->get_sort()));
                else
                    ++powers.insert_if_not_there(arg, 0u);
            }
        }
        if (!coefficient.is_int_perfect_square(root))
            return expr_ref(m);
        expr_ref_vector factors(m);
        if (!root.is_one())
            factors.push_back(mk_numeral(root, e->get_sort()));
        // Every symbolic factor must have even multiplicity. Halving these
        // multiplicities constructs A with e=A*A, without distributing products
        // of sums or assuming anything about the values of symbolic factors.
        for (auto const &kv : powers) {
            expr *arg = &kv.get_key();
            unsigned power = kv.get_value();
            if (power % 2)
                return expr_ref(m);
            for (unsigned i = 0; i < power / 2; ++i)
                factors.push_back(arg);
        }
        if (factors.empty())
            return expr_ref(mk_numeral(rational(1), e->get_sort()), m);
        if (factors.size() == 1)
            return expr_ref(factors.get(0), m);
        return expr_ref(mk_mul(factors), m);
    }
};
