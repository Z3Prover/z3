/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    char_factory.h

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#pragma once

#include "util/uint_set.h"
#include "ast/char_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "model/model_core.h"
#include "model/value_factory.h"

class char_factory final : public value_factory {
    seq_util     u;
    uint_set     m_chars;
    unsigned     m_next { 'A' };
    expr_ref_vector m_trail;

public:
    
    char_factory(ast_manager & m, family_id fid):
        value_factory(m, fid),
        u(m),
        m_trail(m)
    {
    }
        
    expr* get_some_value(sort* s) override {
        m_chars.insert('a');
        return u.mk_char('a');
    }

    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        v1 = u.mk_char('a');
        v2 = u.mk_char('b');
        m_chars.insert('a');
        m_chars.insert('b');
        return true;
    }

    expr* get_fresh_value(sort* s) override {
        while (m_chars.contains(m_next)) 
            ++m_next;
        if (m_next > u.max_char())
            throw default_exception("Character range exhausted");
        m_chars.insert(m_next);
        return u.mk_char(m_next++);        
    }

    void register_value(expr* n) override {
        unsigned ch;
        if (u.is_const_char(n, ch)) 
            m_chars.insert(ch);
    }

    void register_value(unsigned u) {
        m_chars.insert(u);
    }

    void add_trail(expr* e) {
        m_trail.push_back(e);
    }    

};
