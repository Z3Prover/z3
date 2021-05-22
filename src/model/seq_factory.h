/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_factory.h

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "model/model_core.h"
#include "model/value_factory.h"

class seq_factory : public value_factory {
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
    model_core& m_model;
    seq_util     u;
    symbol_set   m_strings;
    unsigned     m_next;
    std::string  m_unique_delim;
    obj_map<sort, expr*> m_unique_sequences;
    expr_ref_vector m_trail;
public:
    
    seq_factory(ast_manager & m, family_id fid, model_core& md):
        value_factory(m, fid),
        m_model(md),
        u(m),
        m_next(0),
        m_unique_delim("!"),
        m_trail(m)
    {
        m_strings.insert(symbol(""));
        m_strings.insert(symbol("a"));
        m_strings.insert(symbol("b"));
    }
    
    void add_trail(expr* e) {
        m_trail.push_back(e);
    }
    
    void set_prefix(char const* p) {
        m_unique_delim = p;
    }
    
    // generic method for setting unique sequences
    void set_prefix(expr* uniq) {
        m_trail.push_back(uniq);
        m_unique_sequences.insert(uniq->get_sort(), uniq);
    }
    
    expr* get_some_value(sort* s) override {
        sort* seq = nullptr;
        if (u.is_seq(s)) 
            return u.str.mk_empty(s);
        if (u.is_re(s, seq)) 
            return u.re.mk_to_re(u.str.mk_empty(seq));
        if (u.is_char(s))
            return u.mk_char('A');
        UNREACHABLE();
        return nullptr;
    }
    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        if (u.is_string(s)) {
            v1 = u.str.mk_string("a");
            v2 = u.str.mk_string("b");
            return true;
        }
        sort* ch;
        if (u.is_seq(s, ch)) {
            if (m_model.get_some_values(ch, v1, v2)) {
                v1 = u.str.mk_unit(v1);
                v2 = u.str.mk_unit(v2);
                return true;
            }
            else {
                return false;
            }
        }
        if (u.is_char(s)) {
            v1 = u.mk_char('a');
            v2 = u.mk_char('b');
            return true;
        }
        return false; 
    }
    expr* get_fresh_value(sort* s) override {
        if (u.is_string(s)) {
            while (true) {
                std::ostringstream strm;
                strm << m_unique_delim << std::hex << m_next++ << std::dec << m_unique_delim;
                std::string s(strm.str());
                symbol sym(s);
                if (m_strings.contains(sym)) continue;
                m_strings.insert(sym);
                return u.str.mk_string(s);
            }
        }
        sort* seq = nullptr, *ch = nullptr;
        if (u.is_re(s, seq)) {
            expr* v0 = get_fresh_value(seq);
            return u.re.mk_to_re(v0);
        }
        if (u.is_char(s)) {
            return u.mk_char('a');
        }
        if (u.is_seq(s, ch)) {
            expr* v = m_model.get_fresh_value(ch);
            if (v) {
                return u.str.mk_unit(v);
            }
            else {
                v = u.str.mk_unit(m_model.get_some_value(ch));
                expr* uniq = nullptr;
                if (m_unique_sequences.find(s, uniq)) {
                    uniq = u.str.mk_concat(v, uniq);
                }
                else {
                    uniq = v;
                }                
                m_trail.push_back(uniq);
                m_unique_sequences.insert(s, uniq);
                return uniq;
            }
        }        
        UNREACHABLE();
        return nullptr;
    }
    void register_value(expr* n) override {
        zstring s;
        if (u.str.is_string(n, s)) {
            symbol sym(s.encode());
            m_strings.insert(sym);
            if (sym.str().find(m_unique_delim) != std::string::npos) 
                add_new_delim();
        }
    }

private:
    
    void add_new_delim() {
    try_again:
        m_unique_delim += "!";
        for (auto const& s : m_strings) 
            if (s.str().find(m_unique_delim) != std::string::npos)
                goto try_again;
    }
};
