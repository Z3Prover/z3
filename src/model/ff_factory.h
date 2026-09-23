#pragma once
#include "ast/ff_decl_plugin.h"
#include "model/value_factory.h"

class ff_factory : public simple_factory<rational> {
    ff_util ff;
    app *mk_value_core(rational const &n, sort *s) override {
        return ff.mk_numeral(n, s);
    }

public:
    explicit ff_factory(ast_manager &m) : simple_factory(m, ff_util(m).get_fid()), ff(m) {}
    expr *get_fresh_value(sort *s) override {
        auto *values = get_value_set(s);
        // A field has exactly p values: never invent an extra element when
        // an array/datatype model asks for a fresh field value.
        while (values->m_next < ff.modulus(s)) {
            bool fresh;
            expr *result = mk_value(values->m_next, s, fresh);
            ++values->m_next;
            if (fresh)
                return result;
        }
        return nullptr;
    }
};
