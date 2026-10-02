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
    app *mk_numeral(rational const &v, sort *s) {
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
    app *mk_app(decl_kind k, unsigned n, expr *const *args) {
        return m.mk_app(m_fid, k, n, args);
    }
    app *mk_add(unsigned n, expr *const *args) {
        return mk_app(OP_FF_ADD, n, args);
    }
    app *mk_add(expr *a, expr *b) {
        expr *args[2] = {a, b};
        return mk_add(2, args);
    }
    template <typename Vec>
    app *mk_add(Vec const &args) {
        return mk_add(args.size(), args.data());
    }
    app *mk_mul(unsigned n, expr *const *args) {
        return mk_app(OP_FF_MUL, n, args);
    }
    app *mk_mul(expr *a, expr *b) {
        expr *args[2] = {a, b};
        return mk_mul(2, args);
    }
    template <typename Vec>
    app *mk_mul(Vec const &args) {
        return mk_mul(args.size(), args.data());
    }
    app *mk_neg(expr *a) {
        return mk_app(OP_FF_NEG, 1, &a);
    }
    app *mk_bitsum(unsigned n, expr *const *args) {
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
        return is_add(e) || is_mul(e) || is_neg(e) || is_bitsum(e) || is_numeral(e);
    }
};
