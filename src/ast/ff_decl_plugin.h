#pragma once
#include "ast/ast.h"

enum ff_sort_kind { FINITE_FIELD_SORT };
enum ff_op_kind { OP_FF_NUM, OP_FF_ADD, OP_FF_MUL, OP_FF_NEG, OP_FF_BITSUM };

class ff_decl_plugin : public decl_plugin {
    vector<rational> m_checked_moduli;

public:
    bool has_sorts() const {
        return !m_checked_moduli.empty();
    }
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
};
