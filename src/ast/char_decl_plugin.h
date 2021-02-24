/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    char_decl_plugin.h

Abstract:

    char_plugin for unicode suppport

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-14

Revision History:

    Updated to string sequences 2015-12-5

    Add SMTLIB 2.6 support 2020-5-17

--*/
#pragma once

#include "util/zstring.h"
#include "ast/ast.h"
#include <string>

enum char_sort_kind {
    CHAR_SORT
};

enum char_op_kind {
    OP_CHAR_CONST,
    OP_CHAR_LE,
    OP_CHAR_TO_INT,
    OP_CHAR_IS_DIGIT
};

class char_decl_plugin : public decl_plugin {
    sort* m_char { nullptr };
    symbol m_charc_sym;
    bool m_unicode { true };

    void set_manager(ast_manager * m, family_id id) override;

public:
    char_decl_plugin();

    ~char_decl_plugin() override;

    void finalize() override {}

    decl_plugin* mk_fresh() override { return alloc(char_decl_plugin); }

    sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override { return m_char; }

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
        unsigned arity, sort* const* domain, sort* range) override;

    void get_op_names(svector<builtin_name>& op_names, symbol const& logic) override;

    void get_sort_names(svector<builtin_name>& sort_names, symbol const& logic) override;

    bool is_value(app* e) const override;

    bool is_unique_value(app* e) const override;

    bool are_equal(app* a, app* b) const override;

    bool are_distinct(app* a, app* b) const override;

    expr* get_some_value(sort* s) override;

    sort* char_sort() const { return m_char; }

    app* mk_char(unsigned u);

    app* mk_le(expr* a, expr* b);

    app* mk_to_int(expr* a) { return m_manager->mk_app(m_family_id, OP_CHAR_TO_INT, 1, &a); }

    app* mk_is_digit(expr* a) { return m_manager->mk_app(m_family_id, OP_CHAR_IS_DIGIT, 1, &a); }

    bool is_le(expr const* e) const { return is_app_of(e, m_family_id, OP_CHAR_LE); }

    bool is_const_char(expr const* e, unsigned& c) const { 
        return is_app_of(e, m_family_id, OP_CHAR_CONST) && (c = to_app(e)->get_parameter(0).get_int(), true);
    }

    bool is_to_int(expr const* e) const { return is_app_of(e, m_family_id, OP_CHAR_TO_INT); }

    bool is_is_digit(expr const* e) const { return is_app_of(e, m_family_id, OP_CHAR_IS_DIGIT); }

    MATCH_UNARY(is_is_digit);
    MATCH_UNARY(is_to_int);
    MATCH_BINARY(is_le);

    bool unicode() const { return m_unicode; }
    unsigned max_char() const { return m_unicode ? zstring::unicode_max_char() : zstring::ascii_max_char(); }
    unsigned num_bits() const { return m_unicode ? zstring::unicode_num_bits() : zstring::ascii_num_bits(); }

};
